# BCEL-derived BN6 family boundary

M196 removes the independently supplied Packet carrier and cut value from the
M195 activation boundary. A `PCCMinCheckedPacketBN6BCELGroupedCells` ledger
supplies only the grouped positive cells and the structural facts needed by
BN6. Its `family` constructor takes the carrier from the computed checked BCEL
nucleus, proves that carrier duplicate-free from the nucleus, takes the cut
value from the nucleus projection defect, and inherits its strict positivity.

The resulting `PCCMinCheckedPacketBN6BCELDerivedFamilyHBData` cannot disagree
with M195 about the carrier or cut value: both equalities hold by reduction.
The M196 resolver therefore reuses M195 while proving its carrier-mismatch and
cut-value-mismatch branches impossible. It preserves the one genuinely open
case—an exact nonempty proper cut whose grouped-cell activation weight differs
from the checked BCEL defect—or returns M195's conditional ZeroSlack result
under complete checked selector silence.

The public theorem is
`PNP.DirectWire.pccmin_checked_packet_bn6_bcel_derived_family_route_or_zeroslack_checked_complete`.
It is general over arbitrary finite direct-wire dimensions, candidates,
candidate-derived saturation models, rank counts, grouped-cell ledgers, and
checked Packet/HB tables. It fixes no circuit, carrier size, cut, Packet,
selector, rank, or table instance.

## Claim boundary

The terminal problem, positive premise, checked ready certificate, grouped
cells and payloads, exact grouping proofs, table, claims, rank assignment,
route-clear result, dependency table, checked HB closure, HResolve,
BudgetResolve, and normalizer remain supplied. In particular, M196 derives the
family skeleton but does not construct the BN3--PkgC--BN6 grouped cells from
every terminal input.

The remaining activation mismatch is diagnostic route evidence. It is not a
verified gain, exact result, or globally decreasing route. The inherited
proper-cut scan may enumerate a powerset and has no encoded-size polynomial
bound. M196 therefore does not complete PkgC/BN3--BN6 integration, prove
manuscript-wide `SaturatePositive` or `BCELReady`, establish unconditional
ZeroSlack, construct polynomial PCCMin, put CNFSAT in P, close a global gate,
create `PNP.Main.p_eq_np`, or prove P = NP.

Formal artefact coverage is 172 of 174 current scoped rows. The separate
risk-weighted proof-completion estimate remains 35 percent, its uncertainty
range remains 20 to 40 percent, and zero of five global gates are closed.

## Verification

```text
lake build PNP
lake env lean -DwarningAsError=true lean-regression/PNPPCCMinCheckedPacketBN6BCELDerivedFamily.lean
lake env lean -DwarningAsError=true lean-audit/PNPPCCMinCheckedPacketBN6BCELDerivedFamilyAxiomAudit.lean
node --test audits/lean-pccmin-checked-packet-bn6-bcel-derived-family0.test.mjs
```

The axiom transcript covers 14 reviewed declarations. Their compiled closure
contains only `propext` and `Quot.sound`; it contains no project-specific axiom,
`sorryAx`, or `Classical.choice`.
