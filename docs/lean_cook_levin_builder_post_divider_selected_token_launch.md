# Lean Cook-Levin post-divider selected-token launch

M215 adds the first all-coordinate token-emission handoff after the literal
M214 post-divider classifier. For every coordinate in the complete
post-header schedule, Lean derives the exact canonical schedule entry rather
than accepting a route, token, or success certificate from a caller.

The checked path is:

1. embed the post-header coordinate after the exact header boundary;
2. reuse M214's physical body-versus-`Finish` classifier with arbitrary
   preserved workspace;
3. prove M210's typed route interpreter equals direct token lookup and the
   proof-carrying entry of the canonical schedule;
4. remove padding slots before the coordinate to obtain the exact emitted
   prefix;
5. leave that prefix unchanged for padding, or run the fixed 59-rule appender
   for the selected body or `Finish` token; and
6. reach exactly the next canonical emitted prefix.

The appender trace is checked twice at its distinct boundaries: exact work
execution and exact six-for-one raw compilation. Removing the final successful
work transition leaves a nonhalting state. The combined staged cost is bounded
by the sum of M214's verifier-derived polynomial and a linear appender term
dominated by source length and the complete token-schedule length.

The public theorem is:

```text
PNP.Concrete.CookLevin.BuilderPostDividerSelectedTokenLaunch.
  cook_levin_builder_post_divider_selected_token_launch_checked_complete
```

It states, for every post-header coordinate, that selection equals the
canonical schedule entry, the physical-classifier and exact-emission contract
holds for arbitrary workspaces, and the combined compiled work is bounded by
one source-size polynomial.

## Claim boundary

The token choice that initializes the appender remains executable Lean
orchestration. M215 does not yet provide one literal raw selector that reads
the M214 tape, inspects the selected clause payload, and enters the appropriate
appender state. It also does not iterate the schedule, construct the complete
formula, prove builder `RawRefinement`, package a `PolynomialReduction`, prove
`CNFSAT in P`, or prove `P = NP`.

The next load-bearing step is the literal post-classifier selector and
workspace bridge. Once that exact handoff exists, the already-proved full
schedule controller must iterate it and the complete builder must be refined
against the canonical formula encoding.
