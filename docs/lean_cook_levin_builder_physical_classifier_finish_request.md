# Lean Cook-Levin physical classifier Finish request

M221 connects the unique canonical `Finish` coordinate of M220's complete
physical classifier pipeline to one literal request-cell write. The new fixed
machine reuses M220's 711-rule classifier, swaps its two terminal verdict names
without changing any transition semantics, and chains the resulting accepting
`Finish` terminal to M219's one-rule writer through the generic nine-symbol
launch table. The combined table therefore has exactly 721 rules.

## Exact derived Finish edge

The endpoint accepts only a concrete `VerifierTableauProblem`; the canonical
`Finish` coordinate is calculated from the verifier-derived schedule rather
than supplied by the caller. For every protected workspace, Lean proves that
M220's classifier reaches its `Finish` terminal with the end marker under the
head, the chained writer runs exactly once, and the final tape is precisely the
classifier tape with that focused cell changed to M217's
`requestSymbol (some .finish)`.

That exact `Tape.write` equation preserves every other cell of the classifier's
terminal tape. The module also proves the complete work trace, the exact
six-transitions-per-work-step compiled trace, collision freedom, and
nonhalting one work step before completion.

The compiled run is bounded by M220's verifier-derived source-size polynomial
plus 12 transitions, accounting for the constant-size chain launch and writer.
No coordinate, request symbol, route, trace, table, certificate, or success
premise is supplied to the public endpoint.

## Public theorem

The certificate-free endpoint is:

```lean
PNP.Concrete.CookLevin.BuilderPhysicalClassifierFinishRequest.
  cook_levin_builder_physical_classifier_finish_request_checked_complete
```

Its exact type records the derived `Finish` coordinate, 721-rule count,
collision freedom, all-workspace execution contract, exact request-cell result,
and uniform polynomial compiled-step bound.

## Claim boundary

M221 closes only the full-classifier-to-`Finish`-request-cell edge. It does not
derive body-token or padding request symbols, reorient the preserved workspace
into M217's dispatcher-ready suffix, run the dispatcher from M220's endpoint,
iterate a literal raw-machine loop, construct the complete formula builder,
prove builder `FunctionProgram.RawRefinement`, or package the Cook-Levin
`PolynomialReduction`. It does not prove CNFSAT NP-hardness, CNFSAT in P, any
global gate, the eligible root theorem, or `P = NP`.
