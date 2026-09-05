# M229: Cook-Levin all-route physical body-remainder split

## Selection rationale and legacy anchor

The pinned legacy manuscript's `TraceEquivalence` lemma and final SAT-decision
section require one uniform concrete Cook-Levin formula builder. The active
reconstruction records that obligation under `Formal.ConcreteSAT` and the open
`reductions-complete-cook-levin-builder` checkpoint.

M228 derives and dispatches the unique `Finish` request, but deliberately stops
every body coordinate at a request-pending marker. M214 already retains the raw
divider quotient and remainder in the physical classifier tape and proves that
the remainder equals the body token coordinate. Repeating those semantic facts
would add no new evidence. The next dependency is a literal fixed machine that
reads the retained tape and branches on whether that physical remainder is zero
or positive. This is the first executable body-selector split needed before
clause occupancy and token payload selection can determine the actual request.

## Unbounded abstraction and bounded theorem target

Construct one fixed finite machine over every
`Fin (BuilderFullScheduleCursorController.bodySlotCount problem)` that:

1. runs M228's all-route derived-Finish machine with no staged request, route,
   remainder, verdict, trace, or success certificate;
2. preserves the completed `Finish` endpoint unchanged;
3. on every body endpoint, crosses the retained clause-count sidecar and safe
   exterior boundaries in the physical tape;
4. skips the raw divider's consumed-dividend marks and inspects the next
   physical symbol;
5. reaches the zero-remainder endpoint exactly when the canonical body token
   coordinate is zero, and the positive-remainder endpoint exactly when that
   coordinate is positive;
6. leaves the builder word and retained classifier ledger intact; and
7. retains collision freedom, exact work, compiled execution,
   one-step-short nonhalting, and one encoded-source-size polynomial bound.

The theorem ranges over the complete verifier-derived post-header schedule.
The machine and its rule table are independent of the source input and schedule
coordinate.

## Exact theorem boundary

Add
`PNP.Concrete.CookLevin.BuilderPhysicalClassifierAllRouteBodyRemainderSplit`
and the endpoint:

```text
PNP.Concrete.CookLevin.
  BuilderPhysicalClassifierAllRouteBodyRemainderSplit.
  cook_levin_builder_physical_classifier_all_route_body_remainder_split_checked_complete
```

The endpoint takes only a `VerifierTableauProblem` and quantifies internally
over every schedule coordinate. Its route-dependent terminal contract keeps
`Finish` complete and identifies zero versus positive body token coordinates
from the physical terminal tape.

## Claim boundary and downstream blockers

M229 does not infer whether a zero-coordinate clause slot is populated or
padding, select a constraint or clause, derive a separator, sign, unary-variable,
clause-terminator, or padding request, connect successive builder configurations,
implement the repeated builder loop, prove builder `FunctionProgram.RawRefinement`,
package the Cook-Levin `PolynomialReduction`, establish concrete NP-hardness or
NP-completeness transport, put `CNFSAT` in `P`, close a fixed checkpoint or
global gate, create the eligible root theorem, or prove `P = NP`.

The fixed risk-weighted score therefore remains 35 percent with the 20 to 40
percent uncertainty range. Formal artefact coverage is regenerated separately.

## Evidence and release gates

1. Compile the changed module, then the root before importing it in audits.
2. Audit every public declaration and run the focused kernel and hostile
   source regressions. Reuse a successful root or axiom result when a later
   edit changes only a regression fixture or publication documentation.
3. Register the theorem and update the expectation chain before extracting
   the compiled inventory, sealing the map, and generating status and reports.
4. Run current authority, publication, progress, archive, documentation-link,
   generated-output and diff-integrity checks; then normal PR and merge gates.
5. Bind PNPLabs to the verified core merge. Its tests own rendering, mirrors,
   links, downloads and deployment evidence; they do not repeat the core Lean
   build. Reproduce the site merge, deploy it, and independently verify production.

The core endpoint and all 71 public axiom closures have passed focused kernel
verification, including literal zero/positive and one-step-short fixtures.
Publication is earned only after the remaining release gates succeed.
