# Canonical Packet colour-route reflection milestone

## Objective

Remove the caller-controlled `colourChecked` bit at the Packet
selector-faithfulness boundary. Every canonical handle already decodes to an
exact grouped footprint with proofs of carrier-sublist membership and
selector-relevant size. The active Packet/HB endpoint should compute an
internal colour check from that data while retaining charge, source-route,
finite-rank, and residual-descent reflection.

## Dependency edge

```text
positive BN6 Packet
  + canonical finite handle and grouped footprint
  + proved carrier-sublist membership and footprint length at least two
  + authoritative rank and supplied before/after residual ranks
  + executable selector silence and HB active-dependency closure
  -> one exact earliest Packet failure
  -> never colour, charge, exactRoute, or rank
  -> either one of five unresolved semantic-field routes
     or proof that the supplied transition is not RankWF-decreasing
```

The construction remains uniform over arbitrary finite grouped BN6 families
and arbitrary finite selector-rank carriers.

## Checked interface

1. Compute the colour Boolean from canonical footprint size; do not reuse the
   payload's caller bit.
2. Retain carrier-sublist membership as a kernel theorem rather than hiding it
   behind proposition-level `decide`.
3. Preserve frontier, obligation, activation, direction, and budget.
4. Retain positive charge, canonical source route, table-owned rank, and exact
   RankWF descent.
5. Prove colour failure and colour first-route outcomes impossible for every
   canonical handle.
6. Preserve charge, rank, exact-route, and final-descent adequacy.
7. Rebuild only table faithfulness while preserving ranks, claims, and blocker
   activity.
8. Pin the reviewed theorem surface in the compiled inventory, publication
   map, axiom transcript, regression, and hostile audit.

## Conservative claim boundary

The reflected colour fact is only internal grouped-footprint eligibility. It
is not an external manuscript colour equivalence or a construction of the
terminal family. The other five semantic fields remain supplied.

This milestone does not establish complete route silence, unconditional HB
negative closure, ZeroSlack, PCCMin, polynomial runtime, SAT in P, or P = NP.

## Release gates

Run the focused source audit, Lean target, regression, and axiom transcript on
the designated remote builder first. Then regenerate compiled inventories,
status, publication map, and canonical report and run the complete core suite
once. Publish through the normal draft-PR, manual-merge,
exact-merge-reproduction, PNPLabs whole-site
audit, deployment, and independent production-verification sequence. PNPLabs
does not rebuild Lean.
