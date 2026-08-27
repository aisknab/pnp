# Canonical sparse V53 constant-cut basis

M199 removes one exponential-looking boundary inherited from M195. The prior
checked endpoint classified constant activation by enumerating every carrier
subset and filtering for nonempty proper cuts. M199 instead proves that the
sparse positive V53 hypergraph structure has an exact canonical basis:

- two anchors require only the full-span footprint weight;
- three anchors require only the three singleton-cut weights, with the three
  complementary pair cuts following from exact crossing symmetry; and
- four or more anchors require every positive cell to be full-span and the
  full-span weight to equal the declared cut value.

For every finite V53 system with at least two anchors,
`PNP.DirectWire.terminalV53_canonicalConstantCutBasis_iff_constantProperCuts`
proves that this basis is equivalent to the complete equation on every
nonempty proper cut. The reverse large-carrier direction proves directly that
a full-span cell crosses every proper cut. The forward large-carrier direction
uses the already checked V53 rigidity result.

`classifyTerminalV53CanonicalConstantCutBasis` is total and proof-bearing. It
returns either accepted basis evidence or one exact structural reason:
insufficient carrier size, a wrong two-anchor full weight, a named
three-anchor singleton mismatch, one concrete non-full cell on a large
carrier, or a wrong large-carrier full weight. Its executable definition does
not call `terminalListSubsets`, enumerate the carrier powerset, or reuse the
M195 all-proper-cut classifier.

At the checked PCC boundary,
`PNP.DirectWire.pccmin_checked_packet_bn6_bcel_canonical_cut_basis_route_or_zeroslack_checked_complete`
runs that classifier over the canonical M197 grouping. An accepted basis
constructs M194's constant-activation input and reuses the checked
Packet/BN6/BCEL/HB contradiction. A rejected basis remains an inhabited typed
route. Every basis cut weight is linked through M198 to the direct supplied raw
positive-cell crossing-mass ledger.

## Claim boundary

The terminal problem, checked BCEL-ready certificate, raw positive cells and
payloads, realizer table, accepted claims, rank assignment, route-clear result,
dependency table, and checked HB closure remain supplied. M199 does not derive
the raw ledger from BN3, BN4, BN5, PkgC, or every terminal input.

A rejected basis is structural diagnostic evidence, not a verified gain or a
globally decreasing transition. Removing this particular powerset scan is not
a complete polynomial-runtime proof: upstream terminal and BCEL construction
may still enumerate subsets, and no uniform encoded-size theorem constructs
all supplied cells, selectors, claims, tables, or blockers.

M199 therefore does not close complete PkgC/BN3--BN6 integration, prove
manuscript-wide `SaturatePositive` or `BCELReady`, establish unconditional
`ZeroSlack`, construct polynomial `PCCMin`, put CNFSAT in P, close a global
gate, create `PNP.Main.p_eq_np`, or prove P = NP.

Formal artefact coverage is 175 of 177 current scoped rows. The separate
risk-weighted proof-completion estimate remains 35 percent, its uncertainty
range remains 20 to 40 percent, and zero of five global gates are closed.

## Verification

```text
lake build PNP
lake env lean -DwarningAsError=true lean-regression/PNPPCCMinCheckedPacketBN6BCELCanonicalConstantCutBasis.lean
lake env lean -DwarningAsError=true lean-audit/PNPPCCMinCheckedPacketBN6BCELCanonicalConstantCutBasisAxiomAudit.lean
node --test audits/lean-pccmin-checked-packet-bn6-bcel-canonical-constant-cut-basis0.test.mjs
```

The axiom transcript covers twenty-two reviewed declarations. Their compiled
closure contains only `propext` and `Quot.sound`; it contains no
project-specific axiom, `sorryAx`, or `Classical.choice`.
