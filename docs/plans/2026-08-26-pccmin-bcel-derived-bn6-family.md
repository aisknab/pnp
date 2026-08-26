# M196 BCEL-derived BN6 family boundary

## Evidence-led selection

M195 compares an independently supplied grouped BN6 family with the checked
finite BCEL-ready nucleus. Two of its three failure branches exist only because
the family is still allowed to carry an independent anchor carrier and cut
value. The pinned manuscript's `RW-BCELReady` and `BN6-HypergraphPacket` route
instead uses one BCEL anchor set and its positive defect throughout the BN3--BN6
construction. The next dependency edge is therefore to construct that part of
the Packet family from the checked nucleus rather than compare duplicate data.

## Legacy anchor and unbounded abstraction

- Legacy anchors: `RW-BCELReady` in Section 10.4, BN3--BN6 and Package C in
  Section 11, and the rank-parametric ZeroSlack contradiction in Section 16 of
  the pinned canonical manuscript.
- Closed edge: checked finite BCEL-ready nucleus plus a grouped-cell ledger ->
  a BN6 family whose carrier is definitionally the computed nucleus and whose
  cut value is definitionally its positive projection defect -> either the
  first proper-cut activation mismatch or M195's coherent BN6/HB conditional
  ZeroSlack branch.
- Unbounded abstraction: arbitrary finite direct-wire dimensions, candidates,
  candidate-derived saturation models, rank counts, grouped-cell ledgers, and
  checked realizer/HB tables. No fixed circuit, anchor count, cut, Packet,
  selector, rank, or table instance can earn this milestone.

## Exact theorem target

Add `PNP.PCCMinCheckedPacketBN6BCELDerivedFamily`. Define a grouped-cell ledger
whose structural fields are exactly the remaining inputs needed to construct a
`TerminalBN6GroupedFamily`. Its constructor must take the carrier and cut value
from the checked `TerminalFiniteBCELReadyCertificate`, prove carrier
duplicate-freedom from the computed nucleus, and prove cut-value positivity
from the nucleus's positive defect. Callers must not supply a family, carrier,
cut value, carrier equality, cut-value equality, or constant-activation proof.

Adapt the constructed family to M195 and eliminate the carrier-mismatch and
cut-value-mismatch branches by their definitional equalities. The only routed
failure at the new boundary is an exact nonempty proper cut whose grouped-cell
activation weight differs from the BCEL defect. The coherent branch may reuse
M195 and M194 to derive conditional ZeroSlack under complete checked selector
silence.

The public endpoint will be
`PNP.DirectWire.pccmin_checked_packet_bn6_bcel_derived_family_route_or_zeroslack_checked_complete`.
It must prove that selector silence yields either zero residual slack or the
exact remaining proper-cut activation mismatch. It must not accept a supplied
classifier result, coherence proof, constant-activation callback, carrier map,
or equality certificate.

## Claim boundary and downstream blockers

The terminal problem, positive premise, checked ready certificate, grouped
cells and payloads, exact grouping proofs, raw realizer table, claims, rank
assignment, dependency table, route-clear result, HResolve, BudgetResolve, and
normalizer remain supplied. M196 derives only the family skeleton; it does not
derive the BN3--PkgC--BN6 grouped cells from every terminal input. The remaining
activation mismatch is diagnostic evidence, not yet a verified gain or a
globally decreasing route. M195's proper-cut scan remains finite but may be
exponential, and no encoded-size or runtime bound is claimed.

Consequently M196 does not prove manuscript-wide `SaturatePositive` or
`BCELReady`, complete PkgC/BN3--BN6 integration, complete global route coverage,
establish unconditional ZeroSlack, construct polynomial PCCMin, put CNFSAT in
P, close a global gate, create the eligible root theorem, or prove P = NP.

No fixed checkpoint changes state. The risk-weighted proof-completion estimate
remains 35 percent, its uncertainty range remains 20 to 40 percent, and zero of
five global gates remain closed. One formal publication evidence row may be
added independently, moving formal artefact coverage to 172 of 174 current
scoped rows.

## Required evidence

- compilation of the new leaf module and the explicit `PNP` root import;
- general regressions for derived carrier identity, derived cut-value identity,
  derived positivity, elimination of the two artificial mismatch branches,
  the remaining activation route, and the route-or-ZeroSlack endpoint;
- an axiom transcript for every reviewed declaration, rejecting project
  axioms, `sorryAx`, and `Classical.choice`;
- hostile checks rejecting a supplied family/carrier/cut value/equality,
  erased activation routes, fixed instances, and unconditional or polynomial
  claims;
- synchronized inventory, publication map, status, progress history, report,
  workflow assertions, audit questions, and current documentation; and
- the normal core and PNPLabs exact-merge, publication-surface, deployment,
  production-verification, notification, evidence-archive, and cleanup gates.

## Stop condition

If the arbitrary-finite derived-family constructor or the elimination of the
carrier and cut-value mismatch branches cannot be proved from the named checked
interfaces, stop at that theorem boundary. Do not replace it with a fixed
family, supplied equality certificate, sampled cuts, new project axiom,
`sorry`, or weakened unconditional claim.
