# Cook-Levin complete schedule iteration

M216 replaces fixed-coordinate publication progress with one all-input,
all-coordinate semantic iteration theorem. For every concrete verifier-tableau
problem, the new recursive runner consumes the complete verifier-derived
post-header schedule and returns the exact canonical `encodeCNFTokens` output.

## What is derived

The only endpoint input is the concrete `VerifierTableauProblem`. The theorem
derives:

- the input-dependent number of post-header opportunities;
- every canonical padding, body-token, and final `Finish` entry;
- the emitted prefix after every bounded iteration count;
- the complete encoded formula token stream at termination;
- M215's physical classifier and appender evidence at every coordinate; and
- one polynomial bound for the aggregate staged compiled work.

No coordinate, token, schedule entry, route certificate, trace, or precomputed
formula is supplied to the endpoint.

## Formal boundary

The recursive function `BuilderCompleteScheduleIteration.run` starts from the
canonical emitted header and applies M215's selected-entry transition at every
post-header coordinate. `run_eq_emittedPrefix` proves every bounded prefix is
the canonical schedule prefix. At the complete body count,
`run_bodySlotCount_eq_encodeCNFTokens` proves exact equality with the full CNF
token encoding.

`accumulatedStagedCompiledSteps_le` sums the already checked per-coordinate
classifier/appender cost. Multiplying the polynomial schedule length by M215's
uniform per-coordinate polynomial gives the aggregate source-size polynomial.

The publication endpoint is:

```text
PNP.Concrete.CookLevin.BuilderCompleteScheduleIteration.cook_levin_builder_complete_schedule_iteration_checked_complete
```

## What remains open

The iteration is executable Lean orchestration over separately checked stages.
It is not one literal raw-machine loop and it does not prove that one stage's
final raw tape is the next stage's initial raw tape. It therefore does not yet
provide the complete builder `RawRefinement`, the packaged Cook-Levin
`PolynomialReduction`, concrete `CNFSAT` NP-hardness, deterministic `CNFSAT` in
`P`, or `P = NP`.

The fixed risk-weighted checkpoint for the complete uniformly polynomial
Cook-Levin formula builder remains open, so M216 does not change the 35% proof
completion estimate. It adds formal artefact coverage only.
