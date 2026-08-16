# Lean exact Packet first-route failure semantics

This milestone gives the existing total Packet first-route classifier its exact
semantics at the checked payload boundary. The previous milestone proved that
every rejected payload returns one of ten closed route values. A route value
was still only a tag: its theorem did not itself expose which supplied field
failed or prove that all earlier fields accepted.

`ResidualTerminalPacketSelectorFirstRouteSemantics` closes that gap uniformly.
For every payload at an arbitrary finite rank, `FailureAt expectedRank route`
states the exact earliest failure named by `route`. Lean proves that
`firstRoute expectedRank = some route` is equivalent to this proposition for
all ten constructors. It also proves that the exact failure is unique and that
checker rejection is equivalent to the existence of one exact failure.

The result lifts through the canonical positive source payload behind every
handle in an arbitrary finite grouped BN6 family. Accepted executable selector
silence and active-dependency closure for the canonicalized HB table already
force a first route from a positive Packet. The new endpoint carries both that
executable equality and the corresponding exact field-failure proposition,
without route-clear or independent binding premises.

## Manuscript anchor and theorem boundary

The pinned manuscript anchors are the Section 14 selector-realization failure
ledger and the Section 16 no-lower ledger. Those interfaces require a failed
route to identify its named field rather than merely produce an unstructured
rejection. This milestone supplies that exact checked-payload interface for
colour, frontier, charge, obligation, activation, direction, budget, rank,
exact-route, and descent failures.

The named endpoint is:

```text
PNP.DirectWire.terminalBN6_packet_computed_faithfulness_hb_first_route_failure
```

Its result is an existential canonical handle and route together with both the
canonical payload's executable `firstRoute` equality and its `FailureAt`
proposition.

## Kernel-checked surface

The source is
[`lean/PNP/ResidualTerminalPacketSelectorFirstRouteSemantics.lean`](../lean/PNP/ResidualTerminalPacketSelectorFirstRouteSemantics.lean).
It provides:

- one closed route-indexed `FailureAt` definition covering all ten fields in
  priority order;
- the exact `firstRoute = some route` equivalence and failure uniqueness;
- the exact rejection/existence equivalence;
- canonical grouped-family definitions and equivalence; and
- the positive-Packet/HB exact-failure theorem and named endpoint.

The regression and axiom audit are:

```text
lean-regression/PNPResidualTerminalPacketSelectorFirstRouteSemantics.lean
lean-audit/PNPResidualTerminalPacketSelectorFirstRouteSemanticsAxiomAudit.lean
audits/lean-residual-terminal-packet-selector-first-route-semantics0.test.mjs
```

The regression exercises each of the ten constructors against both the
executable classifier and its exact proposition, then checks the generic,
grouped-family, uniqueness, rejection, and HB endpoint contracts. The complete
public declaration surface is present in the derived axiom transcript, and all
six theorem declarations are reviewed milestone candidates in the compiled
inventory.

## Failure mode and standard interpretation

This is a standard exact error-classifier result. A colour route means colour
failed. A later route means each earlier check accepted and precisely its named
condition failed. Rank failure is inequality with the expected finite rank;
exact-route and descent failures additionally preserve all earlier acceptance
facts. Two different routes cannot both satisfy `FailureAt` for one payload.

The hostile audit rejects any missing constructor, changed priority, weakened
equivalence, loss of uniqueness, noncanonical payload selection, loss of the
exact field proof at the HB endpoint, or reintroduction of route-clear or
binding premises.

## Claim boundary

`FailureAt` interprets only the existing supplied Boolean payload fields and
finite rank tag. The grouped family, payload construction, rank assignment,
realizer claims, HN/BUD activity, dependency rows, and finite-to-exact rank map
remain explicit inputs. This milestone does not derive any field from terminal
data or prove its external manuscript semantics. It also does not turn a
reported failure into a decreasing complete global outcome system.

Accordingly, it does not establish external selector compatibility, complete
route silence, unconditional HB negative closure, positive slack,
`SaturatePositive`, `BCELReady`, unconditional ZeroSlack, PCCMin, encoded-size
or polynomial-runtime bounds, SAT in P, or `P = NP`.
