# Total Packet selector first-route outcome milestone

## Objective

Close the executable exhaustiveness gap at the current Packet-to-HB boundary.
For every canonical handle in an arbitrary finite grouped BN6 family, prove
that the existing first-route classifier returns `none` exactly when the full
payload checker accepts, and that every rejection returns one of the ten
closed typed routes. Every positive Packet must then expose either a faithful
handle or a first route. Accepted selector silence for the canonicalized HB
table removes the faithful alternative and yields a concrete first-route
witness without assuming route-clear acceptance.

## Legacy anchor and dependency edge

The legacy anchors are the Section 13 Pair packet seed, Balanced-triple seed,
Full-span spine seed, and patched BCEL seed, composed with the Section 14
selector realization contract and Section 15 HB negative-closure route. The
current proof-pipeline audit identifies complete failure naming as a
highest-risk correctness point.

The exact dependency edge is:

```text
positive BN6 Packet
  + canonical payload faithfulness table
  + executable selector silence and HB active-dependency closure
  -> computed canonical payload is nonfaithful
  -> one concrete earliest typed payload-failure route
```

The unbounded abstraction is an arbitrary finite grouped BN6 family and an
arbitrary finite rank carrier. No fixed carrier, rank prefix, or Packet fixture
earns milestone credit.

## Exact theorem boundary

The named endpoint is:

```text
PNP.DirectWire.terminalBN6_packet_computed_faithfulness_hb_first_route
```

For a supplied positive `TerminalBN6PacketConclusion`, typed-realizer table,
dependency table, accepted selector-silence check, and accepted HB
active-dependency closure, it returns a canonical handle and one value of
`TerminalPacketSelectorFaithfulnessRoute` whose equality with the payload's
`firstRoute` is kernel checked. It takes no route-clear premise and no
faithfulness-binding premise.

## Checked interface

1. Prove `firstRoute = none` if and only if the complete payload checker is
   true.
2. Prove checker rejection if and only if some concrete first route is
   returned.
3. Lift both equivalences to the canonical source payload behind any grouped
   family handle.
4. Prove an unconditional faithful-or-first-route outcome for the handle
   supplied by every positive Packet branch.
5. Compose canonical table construction with executable selector silence and
   HB active-dependency closure to eliminate the faithful branch.
6. Pin the exact theorem types in the compiled inventory and publication map,
   with derived axiom and hostile source-shape audits.

## Regression and hostile evidence

- Exercise both payload equivalences and both grouped-family lifts.
- Exercise the positive Packet disjunction and the HB-forced first-route
  witness.
- Reject removal of the checker-to-route equivalence, replacement of the
  canonical payload result, reintroduction of route-clear or binding premises,
  omission of selector silence or HB closure, fixed finite bounds, assumptions,
  and theorem-name overclaims.
- Derive the axiom transcript from every public declaration in the module and
  allow only the repository's reviewed Lean-standard axiom boundary.

## Conservative claim boundary

This milestone proves totality of the already defined data-only classifier. It
does not prove that any field Boolean has the manuscript's external semantics,
that a returned route is semantically valid or decreasing, or that the ten
routes form a complete global outcome system beyond the supplied payload. The
grouped family, payload checks, rank assignment, realizer claims, activity
tables, dependency rows, and exact-rank map remain explicit inputs.

It does not construct those inputs from terminal data, establish full selector
compatibility, complete route silence, unconditional HB negative closure,
`PNP.Main.zero_slack_complete`, PCCMin exactness, encoded-size or
polynomial-runtime bounds, SAT in P, remove a project assumption, or prove
`P = NP`.

## Remaining downstream blockers

1. Derive each payload field and typed route from the terminal candidate and
   map every reported route into a decreasing complete global outcome system.
2. Construct the grouped family, rank assignment, exhaustive realizer claims,
   blocker activity, and dependency rows with external selector compatibility.
3. Close unconditional HB negative closure and ZeroSlack with encoded-size
   bounds.
4. Prove PCCMin loop exactness, polynomial runtime and certificate bounds, then
   the concrete root theorem and final axiom audit.

## Release gates

Run the focused source audit and targeted Lean build before broad checks. Then
regenerate the theorem inventory, formal status, publication map, and canonical
report on the remote builder, run the complete repository suite, and reproduce
the exact commit from a fresh checkout. Use the focused draft-PR, full-check,
manual-merge, exact-merge reproduction, PNPLabs full-surface synchronization,
and production verification sequence.
