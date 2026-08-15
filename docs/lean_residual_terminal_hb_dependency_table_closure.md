# Checked residual-terminal HB dependency-table closure

`lean/PNP/ResidualTerminalHBDependencyTableClosure.lean` advances the supplied
HB graph boundary from an independent edge list to one total dependency table
over every finite HN and budget node.

The result is still conditional on explicit data. It closes finite
representation omissions inside that table. It does not claim that the table
contains the manuscript's semantically correct blocker dependencies.

## Data-only interface

For an arbitrary `rankCount`, `allTerminalPacketHBNodes rankCount` enumerates
both node forms at every finite rank:

```text
TerminalPacketHBNode.hn rank
TerminalPacketHBNode.budget rank
```

`TerminalPacketHBDependencyTable` contains only:

```text
rankTuple    : Fin rankCount -> TerminalResidualRank
dependencies : TerminalPacketHBNode rankCount ->
  List (TerminalPacketHBNode rankCount)
```

The dependency function is total, so every node has a row. There is no
independently supplied edge list and no validity, proof, well-foundedness,
closure, or silence field.

`toGraph` mechanically enumerates every node and maps every dependency in its
row to an edge. `edge_mem_toGraph_iff` and `toGraph_depends_iff` prove exact
representation coverage in both directions. An edge cannot be omitted from a
listed row or added independently of the table.

## Checked proposition

`TerminalPacketHBDependencyTable.check` delegates to the existing exact-rank
graph checker after mechanical materialization. Acceptance is equivalent to:

1. every strict finite-index comparison is preserved by the supplied mapping
   into `TerminalResidualRank.LexLT`; and
2. every dependency in every total row has exact rank strictly below the node
   whose row contains it.

The checker does not accept a caller assertion that the table is complete,
well-founded, cycle-free, or semantically valid.

## Derived closure

From acceptance, Lean proves:

- every node has an exactly represented row;
- every row dependency strictly descends the exact ten-coordinate rank;
- the complete supplied table relation is well-founded;
- every node is accessible;
- no nonempty directed dependency cycle exists; and
- arbitrary predicates admit well-founded induction, provided the caller
  proves the exact local step from all dependencies in each row.

The local-step premise is important. Generic rank induction does not prove a
domain-specific blocker invariant by itself.

## Typed-realizer composition

`TerminalPacketTypedRealizerEvidence.hbTableSound` preserves the existing four
checked outcomes. A gain still carries a genuine strict equivalent gain. An HN
or budget bot still carries its rank bound and active table entry, and now also
names a covered total dependency row. A lower-seed bot still carries a faithful
strictly lower finite rank and now receives strict descent in the exact rank.

`terminalBN6_packet_typed_realizer_hb_dependency_table_closure_contract`
applies this result to every faithful canonical handle in an accepted Packet
typed-realizer table and exposes table validity, total row coverage,
well-foundedness, and cycle exclusion together.

## Audit surface

The source has 21 public declarations. The source-derived axiom transcript
prints every one. Audited theorems reach only Lean's standard `propext` and
`Quot.sound` principles where required. No audited declaration reaches
`Classical.choice`, `sorryAx`, or a project-specific axiom.

Run the focused checks with:

```text
lake env lean -DwarningAsError=true lean-audit/PNPResidualTerminalHBDependencyTableClosureAxiomAudit.lean
lake env lean -DwarningAsError=true lean-regression/PNPResidualTerminalHBDependencyTableClosure.lean
node --test audits/lean-residual-terminal-hb-dependency-table-closure0.test.mjs
```

## Boundary

The dependency rows, finite-to-exact rank mapping, selector family,
faithfulness predicate, blocker activity tables, and realizer claims remain
explicit inputs. Total-table coverage is representation completeness only. It
does not establish blocker semantics, semantic dependency completeness from
terminal data, or the local invariant needed to eliminate active blockers.

Consequently, this result does not establish selector compatibility,
rank-complete selector silence, the full `HB.NegativeClosure`, unconditional
ZeroSlack, PCCMin, polynomial size or runtime, SAT in P, removal of a project
assumption, or P = NP.
