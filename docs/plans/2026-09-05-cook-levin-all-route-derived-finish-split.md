# M228: Cook-Levin all-route derived-Finish request split

## Selection rationale and legacy anchor

The pinned legacy manuscript's `TraceEquivalence` lemma and final SAT-decision
section require one uniform concrete Cook-Levin formula builder. The active
reconstruction records that obligation under `Formal.ConcreteSAT` and the open
`reductions-complete-cook-levin-builder` checkpoint.

M227 gives one fixed terminal-joined classifier, protected-request relay, and
mirrored dispatcher over every body and `Finish` coordinate, but the complete
canonical optional-token request is staged on the initial tape. M219--M223 show
that the unique `Finish` request can instead be derived and dispatched on its
specialized branch. The next bounded dependency is to turn M226's physical
body/`Finish` terminal head into one all-coordinate request-control split with
no staged request cell, dispatching `Finish` and exposing one explicit pending
body-request boundary. This is the finite control interface needed before an
unbounded clause-token request synthesizer can be attached.

## Unbounded abstraction and bounded theorem target

Construct one finite machine over every
`Fin (BuilderFullScheduleCursorController.bodySlotCount problem)` that:

1. runs M226's fixed terminal-joined classifier with a protected canonical
   builder workspace preceded only by one blank sentinel;
2. carries no optional-token request cell on its initial tape;
3. reads the classifier's physical terminal head to select body or `Finish`
   control without a supplied route or verdict;
4. scans the complete blank-free classifier prefix to the protected sentinel;
5. writes a fixed pending-body marker on every body route and writes M217's
   physical `Finish` request on the unique `Finish` route;
6. rejects at the explicit pending-body boundary, while the derived `Finish`
   request runs through the reflected fixed M217 dispatcher to the exact next
   canonical emitted prefix; and
7. retains exact work and compiled execution, one-step-short nonhalting,
   collision freedom, terminal separation, route-specific tape geometry, and
   one encoded-source-size polynomial bound.

The theorem quantifies over the complete verifier-derived post-header schedule.
No caller supplies a request, route, terminal verdict, trace, machine,
polynomial, or success certificate.

## Exact theorem boundary

Add
`PNP.Concrete.CookLevin.BuilderPhysicalClassifierAllRouteDerivedFinishSplit`
and the endpoint:

```text
PNP.Concrete.CookLevin.
  BuilderPhysicalClassifierAllRouteDerivedFinishSplit.
  cook_levin_builder_physical_classifier_all_route_derived_finish_split_checked_complete
```

The endpoint takes only a `VerifierTableauProblem` and quantifies internally
over every schedule coordinate. Its route-dependent terminal contract states
exactly that body coordinates halt at the physical pending-request marker and
the unique `Finish` coordinate appends the canonical final token.

## Claim boundary and downstream blockers

M228 removes the staged optional-token cell and physically closes the common
classifier-terminal-to-body/`Finish` control edge. It derives and dispatches
only `Finish`; it does not derive padding, separator, sign, unary-variable, or
clause-terminator requests on arbitrary body coordinates. It does not select a
constraint or clause from the raw verifier schedule, connect successive
coordinates, implement the repeated builder loop, prove complete builder
`FunctionProgram.RawRefinement`, package the Cook-Levin `PolynomialReduction`,
establish concrete NP-hardness or NP-completeness transport, put `CNFSAT` in
`P`, close a fixed checkpoint or global gate, create the eligible root theorem,
or prove `P = NP`.

The fixed risk-weighted score therefore remains 35 percent with the 20 to 40
percent uncertainty range. Formal artefact coverage is regenerated separately.

## Evidence and release gates

- Build the new module under the pinned Lean toolchain on the configured remote
  builder.
- Add exact all-coordinate body/`Finish` route, absent-staged-request,
  terminal-head, scan, body-pending, derived-Finish dispatch, composite work,
  compiled, one-step-short, collision, and polynomial-bound regressions plus a
  declaration-complete axiom audit.
- Add hostile checks that reject a staged canonical request, supplied route or
  verdict, coordinate-specific machine, body-token synthesis claims, omitted
  body terminal, hidden assumptions, and widened loop, refinement, reduction,
  or complexity claims.
- Import the module through the root and theorem inventory, then regenerate the
  canonical inventory, publication map, status, progress ledger, and report.
