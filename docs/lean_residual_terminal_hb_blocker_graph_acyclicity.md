# Lean residual terminal HB blocker-graph acyclicity

`lean/PNP/ResidualTerminalHBBlockerGraphAcyclicity.lean` reconstructs a
fail-closed finite acyclicity boundary for the HN/BUD blocker graph named in
the pinned manuscript's Section 15 obligations `blockerGraphAcyclicByRank` and
`hbBlockerGraphAcyclic`.

The result is conditional on an explicit data graph.  It does not claim that
the supplied edges are all manuscript blocker dependencies or that any edge
has been derived from a terminal candidate.

## Closed data nodes and edges

`TerminalPacketHBNode rankCount` has exactly two forms:

- `hn rank`; and
- `budget rank`.

Both name a `Fin rankCount` index from the existing typed-realizer interface.
There is no unknown, untyped, silent, or proof-carrying node form.

`TerminalPacketHBDependencyEdge` contains a `blocked` node and the lower-rank
`dependency` node it uses.  The edge has no proof, Boolean validity flag,
semantic assertion, or cycle certificate.  A
`TerminalPacketHBDependencyGraph` contains only:

- a function mapping every finite index to an exact ten-coordinate
  `TerminalResidualRank`; and
- an explicit finite list of edges.

## Exact checks

The rank-embedding checker exhaustively visits every pair of indices in
`allFin rankCount`.  Whenever `lower < upper`, it checks

```text
rankTuple(lower).LexLT rankTuple(upper)
```

with the existing executable projection of the exact manuscript rank order.
This prevents a caller from obtaining the graph theorem with a scrambled
finite-to-exact mapping.

The edge checker independently requires

```text
exactRank(dependency).LexLT exactRank(blocked)
```

for every supplied edge.  `checkRankEmbedding_eq_true_iff`,
`TerminalPacketHBDependencyEdge.check_eq_true_iff`, and
`TerminalPacketHBDependencyGraph.check_eq_true_iff` prove that the Boolean
checks recognize precisely those propositions.

## Well-foundedness and cycle exclusion

`depends_rank_lt` maps every accepted dependency edge into the already proved
well-founded `TerminalResidualRank.LexLT` relation.
`depends_wellFounded` then uses inverse image and subrelation
well-foundedness; it does not accept a caller-supplied termination proof.
`depends_accessible` exposes accessibility of every node.

`noCycle` applies well-foundedness to the nonempty transitive closure and
proves

```text
not (Relation.TransGen graph.Depends node node)
```

for every node.  Thus the exact accepted edge list cannot contain a directed
cycle of any positive length, not merely a self-loop.

## Typed-realizer composition

The finite rank-embedding proof also upgrades every already-valid lower-seed
bot to strict descent in the exact ten-coordinate rank through
`lowerSeed_rankTuple_lt_of_valid`.

`terminalBN6_packet_typed_realizer_hb_acyclicity_contract` composes an accepted
graph with the existing accepted canonical Packet typed-realizer table.  For
every faithful canonical handle it returns:

1. the existing exact four-way gain/HN/budget/lower-seed result;
2. validity of the complete finite-to-exact rank embedding;
3. well-foundedness of the supplied HN/BUD dependency relation; and
4. absence of every nonempty directed cycle in that relation.

## Regression and axiom audit

The regression accepts a two-edge graph containing both an HN-to-budget and a
budget-to-HN dependency at successively smaller exact ranks.  It rejects a
same-rank edge, an upward edge, and a two-node directed cycle.  It also
exercises exact edge descent, accessibility, well-foundedness, cycle
exclusion, exact lower-seed descent, and the canonical typed-table
composition.

The focused transcript audits 22 public declarations:

- 12 have empty axiom closure;
- 1 depends only on `propext`; and
- 9 depend only on `propext` and `Quot.sound`.

No audited declaration reaches `Classical.choice`, `sorryAx`, or a
project-specific axiom.

Run the focused checks with:

```text
lake env lean -DwarningAsError=true lean-audit/PNPResidualTerminalHBBlockerGraphAcyclicityAxiomAudit.lean
lake env lean -DwarningAsError=true lean-regression/PNPResidualTerminalHBBlockerGraphAcyclicity.lean
node --test audits/lean-residual-terminal-hb-blocker-graph-acyclicity0.test.mjs
```

## Boundary

The graph, edges, rank mapping, selector family, faithfulness predicate,
activity tables, and realizer claims remain supplied inputs.  The checker
proves acyclicity only for the exact supplied edges.  It does not prove edge
completeness, blocker semantics, that every active HN or budget row records all
dependencies, or that the rank mapping was constructed from terminal data.
It does not establish selector compatibility, rank-complete selector silence,
or the full `HB.NegativeClosure` theorem.

Accordingly this milestone is not unconditional ZeroSlack, polynomial PCCMin,
`CNFSAT ∈ P`, or `P = NP`, and it removes no project assumption.
