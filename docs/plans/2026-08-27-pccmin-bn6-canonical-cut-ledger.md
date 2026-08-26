# M198: canonical BN6 cut-ledger conservation

## Legacy anchor and dependency edge

- Legacy anchors: BN4's signed activation-mass ledger and BN6's sparse
  hypergraph cellization, where the mass crossing every proper cut must equal
  the same BCEL defect.
- Current formal boundary: M197 constructs the grouped BN6 family from an
  arbitrary finite ledger of raw positive support/payload cells, but the public
  route reports a mismatch only through the derived grouped-family activation
  sum.
- Exact edge closed by M198: prove that coalescing equal canonical footprints
  preserves the raw positive-cell crossing mass for every cut, and expose the
  remaining checked BCEL mismatch directly against that raw ledger.

This is an arbitrary-finite conservation theorem. It must not fix the carrier,
cell count, footprint, payload, cut, selector, rank, candidate, or circuit.

## Construction and theorem target

Define the raw crossing contribution of a positive cell by converting its
normalized support and positive mass to the existing V53 hyperedge interface.
Define the raw positive-cell activation weight as the sum of those contributions.

Prove constructively that:

- collecting atoms at one footprint preserves exactly the sum of the matching
  raw cell masses;
- the duplicate-free canonical footprint universe partitions every raw cell by
  its exact normalized footprint;
- summing active grouped masses over that universe equals the direct raw
  crossing-mass sum for every cut; and
- the M197 grouped family therefore has exactly the raw activation weight.

The public endpoint will be
`PNP.DirectWire.pccmin_checked_packet_bn6_bcel_canonical_cut_ledger_route_or_zeroslack_checked_complete`.
Given the same checked Packet/HB silence premise as M197, it must return either
zero residual slack or one explicit nonempty proper cut where the directly
computed raw positive-cell activation weight differs from the checked BCEL
defect.

The proof must use the canonical list partition and existing V53/V54 crossing
equivalence. It must not enumerate cuts or accept a conservation equality from
the caller.

## Claim boundary and downstream blockers

The terminal problem, checked BCEL-ready certificate, raw positive cells and
their supports/payloads, realizer table, claims, ranks, dependency table,
route-clear result, and checked HB closure remain supplied. M198 does not derive
the raw cells from BN3, BN4, BN5, PkgC, or every terminal input. It does not
prove that a raw-ledger activation mismatch is a gain or globally decreasing
route, construct replacement blueprints or blocker semantics, or establish
semantic dependency completeness.

The canonical finite grouping and ledger sum do not establish an encoded-input-
size polynomial bound for the complete construction. M195's inherited proper-
cut classifier may still enumerate a powerset.

Consequently M198 does not close complete PkgC/BN3--BN6 integration,
manuscript-wide `SaturatePositive` or `BCELReady`, unconditional `ZeroSlack`,
polynomial `PCCMin`, deterministic CNFSAT in P, a global gate, the eligible root
theorem, or P = NP. No fixed progress checkpoint changes state. The
risk-weighted estimate remains 35 percent, the uncertainty range remains 20 to
40 percent, and zero of five global gates remain closed. Formal artefact
coverage may change independently when the publication row is earned.

## Required evidence

- compilation of the generic raw-ledger conservation leaf, the PCCMin adapter,
  and the explicit `PNP` root import;
- general regressions covering duplicate footprints, inactive and active cuts,
  exact mass conservation, the derived-family equality, and the public
  route-or-ZeroSlack endpoint;
- axiom transcripts for every reviewed declaration, rejecting project axioms,
  `sorryAx`, and `Classical.choice`;
- hostile source-contract checks rejecting caller-supplied conservation,
  fixed-cell fixtures as theorem evidence, cut enumeration, erased activation
  routes, and unconditional or polynomial claims;
- synchronized theorem inventory, publication map, status, progress history,
  report, workflow expectations, audit questions, and current documentation;
  and
- the normal exact-merge core evidence followed by the separate PNPLabs
  publication-surface, deployment, and production checks, without rerunning
  Lean in PNPLabs.

## Stop condition

If the arbitrary-finite partition theorem, exact canonical-group activation
equality, or M197 adapter cannot be proved from the named checked interfaces,
stop at that theorem boundary. Do not replace it with a fixed carrier, sampled
cells, a supplied conservation certificate, a new axiom, `sorry`, a weakened
route, or an unconditional claim.
