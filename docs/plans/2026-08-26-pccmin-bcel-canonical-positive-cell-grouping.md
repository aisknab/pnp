# M197: canonical BCEL positive-cell grouping for BN6

## Legacy anchor and dependency edge

- Legacy anchors: the active-minimal-consumer antichain encoding in manuscript
  BN4, the PkgC singletonization edge, and the grouped nonnegative hypergraph
  construction in BN6.
- Current formal boundary: M196 accepts a
  `PCCMinCheckedPacketBN6BCELGroupedCells` value containing already-built V54
  consumer systems, singletonization proofs, a grouped positive payload ledger,
  common-carrier proofs, lower bounds on every footprint, and a proof that the
  grouped footprints are duplicate-free.
- Exact edge closed by M197: derive that complete structural BN6 grouping
  interface from an arbitrary finite list of positive payload cells whose raw
  support lists are normalized against the checked BCEL carrier.

This is an unbounded finite construction. It must not fix the carrier size,
cell count, support, payload, cut, selector, rank, candidate, or circuit.

## Construction and theorem target

Introduce one generic raw positive-cell type. Each cell contains only a support
list and one strictly positive payload-bearing atom. Its canonical footprint is
the checked carrier filtered by support membership, so it is automatically an
order-preserving duplicate-free carrier sublist. Require the footprint to have
length at least two; this is the existing BN6 eligibility boundary, not a new
semantic claim.

Construct the V54 consumer system for a footprint from its singleton consumers.
Prove constructively that its singleton footprint is exactly the normalized
support and that every disjoint consumer pair is singletonized. Compute the
duplicate-free footprint universe from the raw ledger, collect every payload
atom at its exact footprint, and build one grouped cell per canonical footprint.
Prove:

- the canonical footprint universe is duplicate-free and has exactly the raw
  footprints as members;
- every constructed consumer system has the checked BCEL carrier;
- every constructed group has footprint size at least two;
- the constructed group footprints are duplicate-free;
- every input payload atom survives in the unique group at its footprint; and
- no consumer system, singletonization proof, grouping certificate, carrier
  proof, footprint-size proof, or footprint-nodup proof is supplied by the
  caller.

Adapt the resulting groups to M196's
`PCCMinCheckedPacketBN6BCELGroupedCells`, then adapt the new checked Packet/HB
record to M196. The public endpoint will be
`PNP.DirectWire.pccmin_checked_packet_bn6_bcel_canonical_grouping_route_or_zeroslack_checked_complete`.
It must preserve M196's exact result: checked selector silence yields either
zero residual slack or one explicit nonempty proper cut whose constructed
family activation weight differs from the checked BCEL defect.

The implementation must use canonical antichain codes and finite list
normalization. It must not enumerate cuts or carrier powersets to decide group
identity.

## Claim boundary and downstream blockers

The terminal problem, checked BCEL-ready certificate, raw support lists,
positive masses, payload values, realizer table, claims, ranks, dependency
table, route-clear result, and checked HB closure remain supplied. M197 does not
derive the raw cells or their supports and payloads from BN3, BN4, BN5, PkgC,
or every terminal input. It does not prove that the remaining activation
mismatch is a gain or decreasing global route, construct the replacement
blueprints or blocker semantics, or establish semantic dependency
completeness.

The canonical list construction is finite, but this milestone does not prove
an encoded-input-size polynomial bound for the complete upstream and downstream
construction. M195's inherited proper-cut classifier may still enumerate a
powerset.

Consequently M197 does not close complete PkgC/BN3--BN6 integration,
manuscript-wide `SaturatePositive` or `BCELReady`, unconditional `ZeroSlack`,
polynomial `PCCMin`, deterministic CNFSAT in P, a global gate, the eligible root
theorem, or P = NP. No fixed progress checkpoint changes state. The
risk-weighted estimate remains 35 percent, the uncertainty range remains 20 to
40 percent, and zero of five global gates remain closed. Formal artefact
coverage may change independently when the publication row is earned.

## Required evidence

- compilation of the new generic grouping leaf, the PCCMin adapter, and the
  explicit `PNP` root import;
- general regressions covering carrier-normalized footprints, exact singleton
  consumer systems, duplicate coalescing, payload preservation, derived M196
  grouped data, and the public route-or-ZeroSlack endpoint;
- axiom transcripts for every reviewed declaration, rejecting project axioms,
  `sorryAx`, and `Classical.choice`;
- hostile source-contract checks rejecting caller-supplied grouping structures,
  fixed carrier/cell instances, erased activation routes, cut enumeration, and
  unconditional or polynomial claims;
- synchronized theorem inventory, publication map, status, progress history,
  report, workflow expectations, audit questions, and current documentation;
  and
- the normal exact-merge core evidence followed by the separate PNPLabs
  publication-surface, deployment, and production checks, without rerunning
  Lean in PNPLabs.

## Stop condition

If the arbitrary-finite canonical grouping constructor, exact singleton
footprint theorem, payload-preservation theorem, or M196 adapter cannot be
proved from the named checked interfaces, stop at that theorem boundary. Do not
replace it with a fixed carrier, sampled supports, a supplied grouping or
equality certificate, a new axiom, `sorry`, a weakened route, or an
unconditional claim.
