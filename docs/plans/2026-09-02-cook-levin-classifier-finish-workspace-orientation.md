# M222: Cook-Levin classifier Finish-workspace orientation

## Selection rationale and legacy anchor

The pinned legacy manuscript's `TraceEquivalence` lemma and final SAT-decision
section require a uniform concrete SAT construction. The active reconstruction
tracks the incomplete builder under `Formal.ConcreteSAT` and the open
`reductions-complete-cook-levin-builder` checkpoint.

M221 physically derives the unique canonical `Finish` request after M220's
complete classifier, but its preserved builder workspace remains behind the
classifier's routing evidence on the left of the focused request cell. M217's
optional-token dispatcher instead expects the builder workspace on the right.
The next load-bearing edge is therefore a fixed physical orientation pass that
crosses exactly the derived classifier prefix and exposes the request/workspace
geometry needed by the dispatcher route.

## Unbounded abstraction

Range over every concrete polynomial-time verifier problem. Prepend one blank
sentinel to the canonical builder workspace supplied to M221, derive the full
classifier prefix, prove that prefix contains no blank cell, and run a fixed
finite scanner from the generated `Finish` request back to the sentinel. At the
sentinel, write a `Finish` request and halt. The resulting tape must be exactly
the spatial mirror of M217's canonical `Finish`-dispatch entry, with all
classifier evidence retained as exterior data.

The endpoint must expose the exact source and compiled traces, one-step-short
nonhalting, a collision-free fixed rule table, the exact mirrored-entry tape
equation, a derived prefix-size bound, and one verifier-derived source-size
polynomial time bound.

## Exact theorem boundary

Add
`PNP.Concrete.CookLevin.BuilderPhysicalClassifierFinishWorkspaceOrientation`
and the endpoint:

```text
PNP.Concrete.CookLevin.BuilderPhysicalClassifierFinishWorkspaceOrientation.cook_levin_builder_physical_classifier_finish_workspace_orientation_checked_complete
```

The endpoint takes only a `VerifierTableauProblem`. It accepts no supplied
coordinate, classifier verdict, prefix, request cell, orientation trace,
dispatcher tape, polynomial bound, or success certificate.

## Downstream blockers preserved

M222 closes only the physical workspace-orientation edge for the unique
full-classifier `Finish` path. The endpoint proves equality with a spatially
mirrored M217 request-entry tape; it does not claim that M217's existing machine
executes on that mirrored representation.

It does not derive body-token or padding requests, run a mirrored dispatcher,
connect successive schedule configurations, implement one repeated raw-machine
builder loop, prove builder `FunctionProgram.RawRefinement`, package the
Cook-Levin `PolynomialReduction`, establish concrete NP-hardness or
NP-completeness, put `CNFSAT` in `P`, close a fixed checkpoint or global gate,
create the eligible root theorem, or prove `P = NP`.

The fixed risk-weighted score therefore remains 35 percent with the 20 to 40
percent uncertainty range. Formal artefact coverage is regenerated separately.

## Evidence and release gates

- Build the new module under the pinned Lean toolchain on the configured remote
  builder.
- Add exact prefix, sentinel exclusion, scan trace, final geometry, complete
  work and compiled trace, one-step-short, fixed-rule and polynomial-bound
  regressions plus a declaration-complete axiom audit.
- Add hostile checks that reject supplied prefix or orientation data, absent
  sentinels, omitted machine stages, missing traces or bounds, hidden
  assumptions and widened dispatcher, loop, reduction or complexity claims.
- Import the module through the root and theorem inventory, then regenerate the
  canonical inventory, publication map, status, progress ledger and report.
