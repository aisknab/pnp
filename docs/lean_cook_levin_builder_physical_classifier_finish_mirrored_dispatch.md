# Lean Cook-Levin classifier Finish mirrored dispatch

M223 continues M222's complete-classifier `Finish` path through a spatially
reflected copy of M217's optional-token dispatcher. The new source is
`lean/PNP/Concrete/CookLevinBuilderPhysicalClassifierFinishMirroredDispatch.lean`.

## What is constructed

M222 ends with a tape exactly equal to the spatial mirror of M217's canonical
`Finish` request entry. M223 defines a generic reflection for literal work
machines: it swaps the two tape sides, exchanges left and right head moves,
maps the finite rule list, and leaves each query and control state unchanged.
It proves that tape writes and moves commute with reflection, that rule lookup
is preserved, and that every exact source execution transports to an exact
reflected execution.

The reflected M217 dispatcher still has 64 rules. It starts directly on M222's
physical endpoint, executes the canonical `Finish` request, and reaches the
reflection of M217's appender endpoint. The final output is proved equal to the
complete canonical CNF token stream, using the derived fact that the unique
`Finish` coordinate is the final body-schedule coordinate.

The standard total machine bridge chains M222's 740-rule composition to that
reflected dispatcher. The complete table has 813 rules with pairwise-distinct
queries and distinct accepting and rejecting states. No coordinate, request,
output prefix, reflection trace, or success certificate is supplied to the
public endpoint.

The module proves:

- involutive tape and head-move reflection;
- reflection of rule lookup, rule application, work steps and exact runs;
- preservation of dispatcher determinism and terminal-state separation;
- the exact M222-to-reflected-M217 tape handoff;
- the complete 813-rule work trace;
- the exact six-transitions-per-work-step compiled trace;
- nonhalting one work step before completion;
- the reflected appender endpoint with the complete canonical CNF token stream;
  and
- one source-input-size polynomial bound for the compiled run.

## Public theorem

The certificate-free endpoint is:

```lean
PNP.Concrete.CookLevin.BuilderPhysicalClassifierFinishMirroredDispatch.
  cook_levin_builder_physical_classifier_finish_mirrored_dispatch_checked_complete
```

Its only data argument is a `VerifierTableauProblem`. Its type records the
reflection law, fixed 64-rule reflected dispatcher and 813-rule full table,
collision freedom, distinct terminal states, complete execution contract, and
uniform polynomial compiled-step bound.

## Claim boundary

M223 closes only reflected dispatcher execution for the unique
full-classifier `Finish` path. The canonical pre-Finish output is already in
the workspace constructed for this path; M223 does not physically construct
the preceding body and padding requests.

M223 does not derive body-token or padding requests, connect every classifier
outcome to dispatch, connect successive schedule configurations, implement a
repeated physical builder loop, prove builder
`FunctionProgram.RawRefinement`, or package the Cook-Levin
`PolynomialReduction`. It does not prove CNFSAT NP-hardness, CNFSAT in P, any
global gate, the eligible root theorem, or `P = NP`.
