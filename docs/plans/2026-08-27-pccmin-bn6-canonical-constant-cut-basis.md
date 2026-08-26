# M199: canonical sparse constant-cut basis

## Legacy anchor and dependency edge

- Legacy anchors: V53 constant-cut hypergraph rigidity, BN6 sparse positive
  cellization, and the Section 16 requirement that executable routing avoid an
  exponential scan of all anchor cuts.
- Current formal boundary: M198 proves that canonical BN6 coalescing preserves
  the exact raw positive-cell crossing-mass ledger, but the inherited M195
  activation classifier still enumerates the full powerset of the carrier to
  decide whether that ledger equals the checked BCEL defect on every proper
  cut.
- Exact edge closed by M199: exhibit a canonical sparse cut basis whose
  acceptance is equivalent to the complete proper-cut constant equation, and
  use it at the same-candidate checked BN6/BCEL/HB boundary without invoking
  the M195 powerset classifier.

This is an arbitrary-finite theorem. It must not fix the candidate, circuit,
carrier, payload ledger, rank table, or anchor identities.

## Unbounded abstraction and theorem targets

For a finite positive V53 hypergraph with at least two anchors, define the
canonical basis by carrier shape:

- at two anchors, check the exact full-span weight;
- at three anchors, check the three canonical singleton cuts; and
- at four or more anchors, check that every listed positive cell is full-span
  and that the exact full-span weight is the declared cut value.

The large-carrier forward implication must use the already proved V53
rigidity theorem. The reverse implication must prove directly that full-span
cells cross every nonempty proper cut. The two- and three-anchor reverse
implications may use the exact complement symmetry of crossing, but no
powerset enumeration may appear in the executable checker.

The generic reviewed theorem will be
`PNP.DirectWire.terminalV53_canonicalConstantCutBasis_iff_constantProperCuts`:

```text
2 <= system.carrier.length ->
  (system.CanonicalConstantCutBasis <-> system.ConstantProperCuts)
```

The executable classifier must return either that basis evidence or one typed
failure: insufficient carrier, wrong two-anchor full weight, one named
three-anchor singleton mismatch, a concrete non-full cell at four or more
anchors, or a wrong large-carrier full weight.

The public PCCMin endpoint will be
`PNP.DirectWire.pccmin_checked_packet_bn6_bcel_canonical_cut_basis_route_or_zeroslack_checked_complete`.
Under the same complete checked selector-silence premise as M198, it must
return either exact zero residual slack or an inhabited typed canonical-basis
route. Its accepted branch must construct the existing M194 constant-
activation input from the checked basis and reuse the checked Packet/HB
contradiction. It must not call the M195 all-proper-cut classifier.

M198's raw-ledger equality must remain visible at the new boundary: every
canonical cut weight inspected by the basis is definitionally linked, through
the grouped family, to the direct raw positive-cell crossing-mass sum.

## Claim boundary and downstream blockers

The terminal problem, checked BCEL-ready certificate, raw positive cells and
their supports and payloads, realizer table, claims, rank assignment,
route-clear result, dependency table, and checked HB closure remain supplied.
M199 does not derive the raw ledger from BN3, BN4, BN5, or PkgC, and a rejected
basis is a typed structural obstruction rather than a verified gain or a
globally decreasing transition.

The checker removes this particular powerset scan, but M199 proves no encoded-
input-size bound for the complete construction. Upstream terminal and BCEL
searches may still enumerate subsets, and the supplied cells, selectors,
tables, claims, and blockers have no complete generation or polynomial-size
theorem.

Consequently M199 does not close complete PkgC/BN3--BN6 integration,
manuscript-wide `SaturatePositive` or `BCELReady`, unconditional `ZeroSlack`,
polynomial `PCCMin`, deterministic CNFSAT in P, a global gate, the eligible
root theorem, or P = NP. No fixed progress checkpoint changes state. The
risk-weighted estimate remains 35 percent, the uncertainty range remains 20
to 40 percent, and zero of five global gates remain closed. Formal artefact
coverage may change independently when the publication row is earned.

## Required evidence

- compilation of the generic complement/basis theorem, the PCCMin adapter,
  and the explicit `PNP` root import;
- regressions for accepted and rejected two-, three-, and four-plus-anchor
  systems, complement symmetry, exact raw-ledger reflection, and both public
  route-or-ZeroSlack branches;
- axiom transcripts for every reviewed declaration, rejecting project axioms,
  `sorryAx`, and `Classical.choice`;
- hostile source-contract checks rejecting `terminalListSubsets`, reuse of the
  M195 powerset classifier, caller-supplied constant activation, fixed theorem
  carriers, erased structural failures, and unconditional or polynomial
  claims;
- synchronized theorem inventory, publication map, status, progress history,
  report, workflow expectations, audit questions, and current documentation;
  and
- the normal exact-merge core evidence followed by the separate PNPLabs
  publication-surface, deployment, and production checks, without rerunning
  Lean in PNPLabs.

## Stop condition

If the arbitrary-finite basis equivalence, typed total classifier, or checked
PCCMin adapter cannot be proved from the named interfaces, stop at that theorem
boundary. Do not replace it with sampled cuts, a fixed carrier theorem, a
caller-supplied constant equation, a new axiom, `sorry`, a weakened route, or
an unconditional claim.
