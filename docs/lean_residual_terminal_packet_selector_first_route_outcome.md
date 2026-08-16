# Lean total Packet selector first-route outcome

This milestone makes the existing Packet payload classifier total at its
current checked boundary. Previously, acceptance implied that `firstRoute`
returned `none`, and any returned route implied rejection. The converse gap
still allowed a rejected payload to lack a theorem-level route witness.

`ResidualTerminalPacketSelectorFirstRouteOutcome` proves both directions. For
every payload at an arbitrary finite rank, `firstRoute = none` exactly when the
complete data-only checker accepts, and checker rejection exactly when one of
the ten closed route constructors is returned. The same equivalences hold for
the canonical positive source payload behind every handle in an arbitrary
finite grouped BN6 family.

Every positive Packet already contains a canonical handle. Lean now proves
that this handle is either computed faithful or exposes its first route. When
the HB table is canonicalized from those payloads, accepted executable selector
silence and active-dependency closure prove the computed faithfulness bit
false. The named endpoint therefore produces a concrete first-route witness
without a route-clear or independent faithfulness-binding premise.

## Manuscript anchor and theorem boundary

The pinned manuscript anchors are the Section 13 Pair packet seed,
Balanced-triple seed, Full-span spine seed, and patched BCEL seed, composed with
the Section 14 selector realization contract and Section 15 HB
negative-closure route. The theorem closes the current audit obligation that
every failed route be named.

The named endpoint is:

```text
PNP.DirectWire.terminalBN6_packet_computed_faithfulness_hb_first_route
```

Its result is an existential canonical handle, an existential value of the
existing closed route type, and an equality proving that the canonical
payload's executable `firstRoute` returns that value.

## Kernel-checked surface

The source is
[`lean/PNP/ResidualTerminalPacketSelectorFirstRouteOutcome.lean`](../lean/PNP/ResidualTerminalPacketSelectorFirstRouteOutcome.lean).
It provides:

- exact no-route/acceptance and route/rejection equivalences for one payload;
- exact lifts of both equivalences to canonical grouped-family handles;
- `existsFaithfulOrFirstRoute`, a total positive-Packet outcome; and
- `existsFirstRoute_of_computedTableSelectorSilence` plus the named endpoint,
  which remove the faithful side using the accepted canonical HB checks.

The regression and axiom audit are:

```text
lean-regression/PNPResidualTerminalPacketSelectorFirstRouteOutcome.lean
lean-audit/PNPResidualTerminalPacketSelectorFirstRouteOutcomeAxiomAudit.lean
audits/lean-residual-terminal-packet-selector-first-route-outcome0.test.mjs
```

All seven public theorem declarations are included in the derived axiom
transcript and compiled theorem inventory.

## Failure mode and standard interpretation

This is a standard total classifier result over a finite tagged error type. A
successful check has no error tag. A failed check has the earliest tag in the
fixed priority order. The hostile audit rejects any change that drops the
equivalence, changes canonical-payload selection, retains a generic rejection
without a route, or reintroduces route-clear or binding premises into the named
HB outcome.

The route value is evidence about these checked Boolean fields only. It is not
evidence that the corresponding manuscript obstruction holds in external
terminal data.

## Claim boundary

The grouped family, payload-field Booleans, finite rank tags and rank map,
realizer claims, HN/BUD activity, dependency rows, and finite-to-exact rank map
remain explicit inputs. This milestone does not derive them from a terminal
candidate or prove their external semantics. It also does not show that a
returned route decreases a complete global outcome system.

Accordingly, this milestone does not establish external selector
compatibility, complete route silence, unconditional HB negative closure,
positive slack, `SaturatePositive`, `BCELReady`, unconditional ZeroSlack,
PCCMin, encoded-size or polynomial-runtime bounds, SAT in P, or `P = NP`.
