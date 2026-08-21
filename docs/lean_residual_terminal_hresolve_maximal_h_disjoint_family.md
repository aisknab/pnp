# Terminal HResolve maximal H-disjoint family

`lean/PNP/ResidualTerminalHResolveHDisjointFamily.lean` formalizes the
finite family-assembly step named in the manuscript's HResolve boundary. A
hereditary footprint carries separate finite support, frontier, origin,
kernel, obligation, prefix-tail, charge, and interface coordinates.
`TerminalHereditaryFootprint.HDisjoint` means simultaneous noninterference in
all eight domains, and `checkHDisjoint` is proved equivalent to that exact
proposition.

`terminalHResolveGreedyHDisjointFamily` recursively processes an arbitrary
finite supplied family. It keeps a footprint precisely when that footprint is
H-disjoint from the family already selected from the tail. Lean proves that
the result contains only governed footprints, preserves duplicate-freedom,
and is a maximal pairwise H-disjoint family. The maximality proof is
proof-relevant:
every governed footprint is selected, or it names a selected blocker together
with the first exact support, frontier, origin, kernel, obligation,
prefix-tail, charge, or interface interference route.

The named bounded endpoint is
`PNP.DirectWire.terminal_hresolve_maximal_hdisjoint_family_complete`.
Its proof is generic in the family length and all eight coordinate types. The
regression exercises all eight route constructors and a nontrivial rejected
candidate whose blocker remains in the selected family.

## Evidence

```text
lake env lean -DwarningAsError=true lean-audit/PNPResidualTerminalHResolveHDisjointFamilyAxiomAudit.lean
lake env lean -DwarningAsError=true lean-regression/PNPResidualTerminalHResolveHDisjointFamily.lean
node --test audits/lean-residual-terminal-hresolve-maximal-h-disjoint-family0.test.mjs
```

The axiom transcript covers every public declaration in source order. The
hostile audit rejects omitted coordinate domains, caller-supplied success,
non-maximal selection, erased blocker routes, fixed family bounds,
assumptions, and widened claims.

## Boundary

The hereditary footprints remain supplied. This result does not derive HN
leaves from a terminal candidate, formalize the pair/tripod/spine/non-flat
grammar, prove BWL exactness or ParseOrExit, establish leaf tightness, solve a
leaf, build the full H0-H4 `NoHereditary` sidecar, or connect blockers to HB
ranks. It is not full or polynomial HResolve, the complete no-lower ledger,
unconditional ZeroSlack, PCCMin, a polynomial-runtime result, SAT in P, or
`P = NP`.
