# PkgC-to-BN6 positive cellization

M201 connects the existing PkgC same-key cancellation classifier to the raw
positive-cell interface consumed by canonical BN6 grouping. The theorem is
uniform over an arbitrary finite source-cell list, common carrier, payload
type, full-candidate type, and complete BN5 restoration-coordinate types.

Each source cell contains a finite minimal-consumer system over the common
carrier, one cut where that system is genuinely active on both sides, and one
strictly positive payload atom. It does not contain a BN6 support list or a
footprint-size certificate.

The total classifier visits the source list in order. For each system it runs
the proof-bearing PkgC same-key classifier. A nonsingleton separating pair is
returned with its exact source-cell membership, separating-pair data, typed
full candidates, complete-coordinate preservation, balanced opposite-sign
BN4 ledger, empty same-key residual, and zero signed mass. No Boolean route
label replaces this evidence.

If every system reaches the singletonized branch, Lean applies V54 to the
source cell's active cut. The cut supplies two distinct singleton consumers on
opposite sides, so the singleton footprint has length at least two. Because
the footprint is already a duplicate-free sublist in carrier order, BN6
normalization is the identity. The resulting `TerminalBN6PositiveCell` is
therefore constructed from the consumer system itself.

For every cut, the constructed cell's hyperedge-crossing bit equals the
original system's two-sided activation bit. Mapping this construction over the
arbitrary finite source list preserves list length and payload order and proves
the exact ledger equation

```text
terminalBN6PositiveCellsActivationWeight carrier constructedCells cut =
  terminalPkgCBN6SourceActivationWeight sourceCells cut.
```

The public endpoint is
`PNP.DirectWire.terminalPkgC_bn6_positive_cellization_checked_complete`.

## Claim boundary

The consumer systems, positive payload atoms, typed restoration operation,
and proof that restoration preserves the complete coordinate remain supplied.
M201 does not derive them from a terminal candidate or construct the upstream
BN3/BN4/BN5 ledger. A returned PkgC cancellation is proof-bearing local
evidence, but it is not yet mapped to a verified global gain or rank-decreasing
transition.

M201 constructs the BN6 raw supports only on the all-singletonized branch and
proves their activation conservation. It does not establish the BCEL
constant-cut equation, checked Packet tables, complete PkgC/BN3--BN6 route
integration, selector faithfulness, blocker semantics, semantic dependency
completeness, complete route silence, encoded-input polynomial construction or
runtime, unconditional ZeroSlack, polynomial PCCMin, CNFSAT in P, the eligible
root theorem, or P = NP.

Formal artefact coverage is 177 of 179 current scoped rows. The separate
risk-weighted proof-completion estimate remains 35 percent, its uncertainty
range remains 20 to 40 percent, and zero of five global gates are closed.

## Verification

```text
lake build PNP
lake env lean -DwarningAsError=true lean-regression/PNPResidualTerminalPkgCBN6PositiveCellization.lean
lake env lean -DwarningAsError=true lean-audit/PNPResidualTerminalPkgCBN6PositiveCellizationAxiomAudit.lean
node --test audits/lean-residual-terminal-pkgc-bn6-positive-cellization0.test.mjs
```

The axiom transcript covers nineteen reviewed declarations. Every declaration
reaches only the approved Lean-standard closure (`propext` and, where needed,
`Quot.sound`); no project-specific axiom, `sorryAx`, or `Classical.choice` is
present.
