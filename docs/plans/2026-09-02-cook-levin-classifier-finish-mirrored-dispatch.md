# M223: Cook-Levin classifier Finish mirrored dispatch

## Selection rationale and legacy anchor

The pinned legacy manuscript's `TraceEquivalence` lemma and final SAT-decision
section require a uniform concrete SAT construction. The active reconstruction
tracks the incomplete builder under `Formal.ConcreteSAT` and the open
`reductions-complete-cook-levin-builder` checkpoint.

M222 takes the unique `Finish` request produced by the complete physical
classifier and reaches exactly the spatial mirror of M217's canonical
dispatcher entry. The next load-bearing edge is therefore to make that
geometric equality executable: reflect M217's literal machine semantics and
chain the reflected dispatcher directly after the complete M220--M222 path.

## Bounded theorem target

Define spatial reflection once for arbitrary finite work machines. Reflection
swaps the tape's left and right sides, exchanges left and right head moves,
maps every literal rule without changing its query or state, and preserves the
machine's start, accept and reject states. Prove that one reflected step and
every exact reflected run commute with the corresponding source execution.

Specialize this construction to M217's fixed 64-rule dispatcher and M222's
unique full-classifier `Finish` endpoint. Chain both machines through the
standard total bridge. The resulting fixed 813-rule machine must execute from
the complete classifier entry to the reflected M217 appender endpoint whose
output is the complete canonical CNF token encoding.

The endpoint must expose the reflection law, exact source and compiled traces,
one-step-short nonhalting, collision-free fixed tables, the physical handoff,
the complete canonical output, and one verifier-derived source-size polynomial
time bound.

## Exact theorem boundary

Add
`PNP.Concrete.CookLevin.BuilderPhysicalClassifierFinishMirroredDispatch`
and the endpoint:

```text
PNP.Concrete.CookLevin.BuilderPhysicalClassifierFinishMirroredDispatch.cook_levin_builder_physical_classifier_finish_mirrored_dispatch_checked_complete
```

The endpoint takes only a `VerifierTableauProblem`. It accepts no supplied
coordinate, request, output prefix, classifier result, mirrored trace, machine,
polynomial bound, or success certificate.

## Downstream blockers preserved

M223 closes only reflected M217 execution for the unique full-classifier
`Finish` path. Reaching the complete token encoding at this endpoint assumes
the canonical pre-Finish emitted prefix already present in M222's constructed
workspace; it does not construct all preceding body and padding requests in
one physical run.

It does not derive body-token or padding requests, connect every classifier
outcome to dispatch, connect successive schedule configurations, implement one
repeated raw-machine builder loop, prove builder
`FunctionProgram.RawRefinement`, package the Cook-Levin
`PolynomialReduction`, establish concrete NP-hardness or NP-completeness, put
`CNFSAT` in `P`, close a fixed checkpoint or global gate, create the eligible
root theorem, or prove `P = NP`.

The fixed risk-weighted score therefore remains 35 percent with the 20 to 40
percent uncertainty range. Formal artefact coverage is regenerated separately.

## Evidence and release gates

- Build the new module under the pinned Lean toolchain on the configured remote
  builder.
- Add exact reflection, step transport, run transport, Finish handoff, complete
  output, full work and compiled trace, one-step-short, fixed-rule and
  polynomial-bound regressions plus a declaration-complete axiom audit.
- Add hostile checks that reject an unreflected dispatcher, changed head-move
  reflection, incomplete output, omitted machine stages, missing traces or
  bounds, hidden assumptions and widened loop, reduction or complexity claims.
- Import the module through the root and theorem inventory, then regenerate the
  canonical inventory, publication map, status, progress ledger and report.
