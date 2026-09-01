# M220: Cook-Levin all-coordinate physical classifier pipeline

## Selection rationale and legacy anchor

The pinned legacy manuscript's `TraceEquivalence` lemma and final SAT-decision
section rely on a uniform concrete SAT construction.  The active reconstruction
records the missing uniform builder under `Formal.ConcreteSAT` and the open
`reductions-complete-cook-levin-builder` checkpoint.

M213 proves the exact physical router-to-divider tape bridge and runs the raw
divider for every post-header coordinate.  M214 separately proves the exact
divider-to-classifier bridge and the body-versus-`Finish` comparator.  Their
terminal and initial tapes are propositionally equal, but the stages are not yet
one machine execution.  M219 therefore has to start at the final comparator for
its unique `Finish` branch.  The next load-bearing edge is to compose the four
already checked machines before attempting request generation.

## Unbounded abstraction

Range over every concrete polynomial-time verifier problem, every canonical
post-header coordinate and arbitrary builder workspace.  Use one fixed nested
`WorkMachineChain` containing M213's tape bridge, M211's divider, M214's
post-divider bridge and the shielded body-versus-`Finish` comparator.

The endpoint must derive the equal or greater outer-router branch from the
coordinate.  It must expose exact stage-to-stage tape equality, the complete
work trace, the compiled six-for-one trace, one-step-short nonhalting, a
collision-free fixed rule table and one verifier-derived source-size polynomial
bound.  The final state must agree with M214's decoded body-versus-`Finish`
classification.

## Exact theorem boundary

Add `PNP.Concrete.CookLevin.BuilderPhysicalClassifierPipeline` and the endpoint:

```text
PNP.Concrete.CookLevin.BuilderPhysicalClassifierPipeline.cook_levin_builder_physical_classifier_pipeline_checked_complete
```

The endpoint takes only a `VerifierTableauProblem`.  Its per-coordinate clause
quantifies over a bounded post-header index and arbitrary workspace.  It accepts
no supplied outer route, comparison result, quotient, remainder, classifier
verdict, trace or success certificate.

## Downstream blockers preserved

M220 classifies every canonical post-header coordinate through one fixed
physical pipeline, but it does not translate a body classification into a
padding or token request.  It does not write any request symbol, run M217's
dispatcher, connect successive schedule configurations, implement one repeated
builder loop, prove builder `FunctionProgram.RawRefinement`, package the
Cook-Levin `PolynomialReduction`, establish concrete NP-hardness or
NP-completeness, put `CNFSAT` in `P`, close a fixed checkpoint or global gate,
create the eligible root theorem, or prove `P = NP`.

The fixed risk-weighted score therefore remains 35 percent with the 20 to 40
percent uncertainty range.  Formal artefact coverage is regenerated
separately.  The currently stale overview coverage sentence in `README.md` must
also be reconciled from the generated M220 authority rather than copied forward.

## Evidence and release gates

- Build the new module under the pinned Lean toolchain on the configured remote
  builder.
- Add all-coordinate branch, exact handoff, complete work and compiled trace,
  one-step-short, fixed-rule and polynomial-bound regressions plus a
  declaration-complete axiom audit.
- Add hostile checks that reject supplied routing or arithmetic inputs, omitted
  physical stages, absent branch agreement, missing traces or bounds, hidden
  assumptions and widened request, loop, reduction or complexity claims.
- Import the module through the root and theorem inventory, then regenerate the
  canonical inventory, publication map, status, progress ledger and report.
