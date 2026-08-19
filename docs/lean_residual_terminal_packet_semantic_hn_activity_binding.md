# Checked Packet semantic/HN activity binding

This milestone closes the local checked dependency edge between the four
remaining exact non-budget Packet routes and the finite HB
hereditary-normalization activity table. It does not claim global route
silence or ZeroSlack.

## Exact checked interface

For every canonical handle in an arbitrary finite grouped BN6 family,
`checkPacketSemanticHNActivityBinding` checks:

```text
(source frontier = selector frontier
 and source obligation = selector obligation
 and source activation atom = selector activation atom
 and source direction = selector direction)
or
hnActive(rankOf(handle)) = true
```

The handle list is the family's existing complete input-relative enumeration,
and `rankOf` is the typed-realizer table's authoritative finite rank. There
is no separate success flag and no fixed selector or rank bound.

`checkPacketSemanticHNActivityBinding_eq_true_iff` proves that this Boolean
scan is exactly the proposition that every failure of the four-field
agreement activates the corresponding ranked HN node.

## Composition with HB closure

The existing `checkNoOutcomeActiveClosure` checker independently validates
the strict exact-rank dependency table and the local active-to-active closure
condition. Its well-founded induction theorem proves every HN and budget
activity bit false.

Therefore
`packetSemanticFieldsAgree_of_checkedHNActivityBinding` combines the two
accepted checks to prove exact frontier, obligation, activation, and
direction equality at every canonical handle.
`packetSelectorSemanticFirstRoutes_ne_of_checkedHNActivityBinding` then
proves that the canonical first-route classifier cannot return any of
`.frontier`, `.obligation`, `.activation`, or `.direction`.

The named endpoint
`terminalBN6_packet_semantic_hn_activity_bound_descent_failure` composes this
with the separately checked budget/HB binding, positive Packet existence, and
executable selector silence. The forced route is exactly `.descent`;
`FailureAt` remains tied to that route and supplies the exact proof that the
after-rank is not lexicographically below the before-rank.

## Audit surface

- `lean/PNP/ResidualTerminalPacketSemanticHNActivityBinding.lean`
- `lean-regression/PNPResidualTerminalPacketSemanticHNActivityBinding.lean`
- `lean-audit/PNPResidualTerminalPacketSemanticHNActivityBindingAxiomAudit.lean`
- `audits/lean-residual-terminal-packet-semantic-hn-activity-binding0.test.mjs`

The regression accepts four-field agreement without activity, accepts each
individual mismatch only with the authoritative HN activity bit, rejects each
inactive mismatch independently, and shows that an active mismatch cannot
simultaneously pass the independently ranked no-outcome closure.

## Boundary

The grouped family, BN5 coordinates, activation atoms, typed directions and
budgets, rank map, residual ranks, realizer claims, activity table, dependency
rows, and both checked bindings remain explicit data. This milestone does not
construct the Packet-to-HN binding from terminal data, establish HN blocker
semantics or semantic dependency completeness, derive the HB tables, or
implement a complete external Packet adequacy bridge.

The sole returned route proves residual nondecrease. It does not construct a
decreasing transition or a no-lower contradiction. The theorem does not prove
unconditional HB negative closure, the no-lower ledger, ZeroSlack, PCCMin,
encoded-size or polynomial-runtime bounds, SAT in P, removal of a project
assumption, or P = NP.
