# Residual terminal HB blocker-graph acyclicity milestone

## Objective

Extend the checked Packet typed-realizer boundary with a finite, data-only
HN/BUD dependency graph.  Every declared dependency edge must descend under
the already formalized ten-coordinate `TerminalResidualRank.LexLT` order.
Acceptance must therefore yield a kernel-checked well-founded dependency
relation and rule out a directed cycle in the exact supplied graph.

## Why this milestone is next

The current typed-realizer contract admits only verified gains, active HN or
budget bots, and faithful strictly lower finite-rank seeds.  It deliberately
does not check the dependency graph behind the HN/BUD tables.  The public HB
review boundary identifies circular blocker justification as the next local
failure mode, and the repository already contains the exact manuscript rank
order needed to reject it without adding an assumption.

## Checked interface

1. Define closed HN and budget node forms indexed by the existing arbitrary
   finite rank carrier.
2. Define data-only directed dependency edges and a graph containing an
   explicit finite edge list plus an explicit mapping from finite rank indices
   to exact ten-coordinate residual ranks.
3. Check every edge, with no proof fields, by requiring the dependency node's
   exact rank to be strictly below the node it supports.
4. Prove the Boolean checker recognizes the edgewise proposition exactly.
5. Derive exact-rank descent for every graph edge, accessibility of every
   node, well-foundedness of the supplied dependency relation, and absence of
   a nonempty directed cycle.
6. Compose accepted graph evidence with the existing accepted canonical
   Packet typed-realizer table so a faithful handle receives its existing
   four-way result while the supplied HN/BUD dependency relation is
   independently known to be well-founded.

## Regression and hostile evidence

- Accept an explicit descending graph containing both HN-to-budget and
  budget-to-HN edges at successively smaller exact ranks.
- Reject a same-rank edge, an upward edge, and a two-node cycle.
- Exercise exact checker equivalence, edge descent, accessibility,
  well-foundedness, no-cycle, and typed-table composition.
- Derive the axiom transcript from every declaration in the new module and
  forbid assumptions, shortcuts, fixed rank bounds, project axioms, and
  theorem-name overclaims.
- Pin only the reviewed public theorems in the compiled inventory and formal
  publication map.

## Conservative claim boundary

The graph, its edge list, the finite-to-exact rank mapping, selector family,
faithfulness table, blocker activity tables, and realizer claims remain
explicit inputs.  Acceptance proves acyclicity only for the supplied edges.
It does not prove that the edge list is complete, that an edge has the
manuscript's blocker semantics, that an active HN or budget row has all of its
dependencies recorded, or that the finite indices or supplied mapping were
constructed from terminal data.  It does not establish selector compatibility
or rank-complete selector silence, construct a replacement or blocker, prove
the full `HB.NegativeClosure`, ZeroSlack, PCCMin, polynomial size/runtime,
SAT in P, remove a project assumption, or prove P = NP.

## Release gates

Run the focused Lean transcript and regression first, then the hostile Node
audit, inventory/publication regeneration checks, full repository verification,
and a fresh clean exact-commit reproduction.  Publish through a focused draft
PR, require every normal check, merge manually, and reproduce the merge before
the corresponding full-surface PNPLabs synchronization and production gates.
