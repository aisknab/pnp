# Lean V53 constant-cut hypergraph rigidity

`lean/PNP/ResidualTerminalConstantCutHypergraphRigidity.lean` reconstructs the
manuscript's theorem V53 over an arbitrary finite anchor carrier. It consumes a
sparse nonnegative weighted hypergraph whose legal footprints are distinct
carrier-ordered sublists of size at least two and whose every nonempty proper
cut has one declared positive crossing value `D`.

The source first proves exact mass conservation for every cut:

```text
inside(S) + inside(A \ S) + cut(S) = total
```

Comparing the equation for a singleton cut with the equation for a pair cut
isolates the exact pair weight as a region difference. Every footprint in that
difference is therefore bounded by the pair weight. Pairs sharing an anchor
have equal weight. When the carrier has at least four anchors, two distinct
outside pairs occur in the same difference, forcing the common pair weight to
zero. Positivity then forces every listed proper hyperedge to disappear.

The named theorem
`PNP.DirectWire.terminalV53_constantCut_hypergraph_rigidity` proves all three
finite cardinality branches:

- `q = 2`: the full-span weight is `D`;
- `q = 3`: every pair has one common weight `p` and the full-span weight
  satisfies `w_A + 2p = D`;
- `q >= 4`: every proper footprint has weight zero and the full-span weight is
  `D`.

The theorem is not a fixed instance: its atom type and duplicate-free finite
carrier are arbitrary, and no `Fin` cardinality or hard-coded cut coordinate
appears in the source theorem. The sparse representation records positive
cells explicitly and assigns implicit zero weight to every omitted footprint.

The regression file checks a two-anchor full edge, a mixed three-anchor model
with three unit pairs and one unit full edge, a four-anchor full-span-only
model, and hostile unequal-pair data that fails the constant-cut premise. The
axiom transcript covers all 58 public declarations and admits only the
project's standard `propext` and `Quot.sound` allowlist; it rejects
`Classical.choice`, `sorryAx`, and project theorem assumptions.

Run the focused checks with:

```sh
lake env lean -DwarningAsError=true lean-audit/PNPResidualTerminalConstantCutHypergraphRigidityAxiomAudit.lean
lake env lean -DwarningAsError=true lean-regression/PNPResidualTerminalConstantCutHypergraphRigidity.lean
node --test audits/lean-residual-terminal-constant-cut-hypergraph-rigidity0.test.mjs
```

This closes only V53's constant-cut classification after V54's explicit
consumer-antichain normal form. It does not construct PkgC, derive the
hypergraph from a terminal candidate, build the BN6 cellization or payloads,
complete global routes or selectors, establish polynomial generation or
runtime, prove ZeroSlack or PCCMin, put SAT in P, or prove `P = NP`.
