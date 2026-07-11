# Lean local framed machine simulation

`lean/PNP/Concrete/PipelineMachineSimulation.lean` is the first executable layer above the
boundary geometry. It translates the ordered rules of one raw `Machine` into a finite
`WorkMachine` that operates on a tape satisfying `PipelineTape.Represents`.

## Exact local and finite-run results

For one successful source transition

```lean
step? machine raw = some next
```

and any represented work tape, Lean constructs an exact three-transition work run whose final
configuration represents `next`. Interior and stay paths use harmless padding so the cost is
uniform. Empty-side left and right moves shift the corresponding marker across one arbitrary
exterior work symbol; every one of the nine possible exterior symbols is covered.

The existing literal work-machine compiler exposes the corresponding ordinary raw-machine run.
With fuel eighteen, `run` from `encodeWorkConfiguration` reaches the encoded final work
configuration. The theorem is an equality for the at-most interpreter; it does not separately claim
that all eighteen transitions succeed.

The same module defines `rawRunExact?`, which rejects if the source execution stops before its
stated length. For any witness

```lean
rawRunExact? machine n start = some final
```

and any work tape representing `start.tape`, Lean constructs exactly `3 * n` successful work steps
to a work configuration representing `final`. Ordinary compiled-machine `run` with fuel `18 * n`
reaches that work configuration's encoding. Both multipliers are indexed by the supplied source
transition count `n`; neither is a bound in the bit-length of an external input.

## Selection and halting discipline

Raw rule order is preserved. Conflicting duplicate left-hand sides remain legal, and the simulator
uses the same first matching rule as `Machine.findRule`. Source rules whose state is a designated
accept or reject state are omitted because `Machine.step?` checks halting before rule lookup.
Fresh sentinel states separate simulator control from source states and intermediate phases.

A stuck nonhalting raw configuration is not treated as successful or rejecting. The one-step theorem
requires an actual `some next` source step, and `rawRunExact?` fails if any of its `n` requested
steps has no successor. This is not `boundedDecide` semantics: it supplies no timeout or verdict
correspondence. Malformed data/marker layouts receive no correctness claim.

## Audit

```bash
lake build PNP
lake env lean -DwarningAsError=true \
  lean-audit/PNPConcretePipelineMachineSimulationAxiomAudit.lean
node --test audits/lean-concrete-pipeline-machine-simulation0.test.mjs
```

The static audit pins the closed imports and complete declaration surface, rejects hidden
assumptions and proof shortcuts, checks ordered first-match construction and terminal-source
suppression, and exercises hostile changes to markers, directions, state separation, exact
`3 * n` work accounting, and the compiled `18 * n` fuel bound. The dedicated Lean transcript
prints the axiom closure of every explicit declaration.

## Exact nonclaim

This is an exact-successful-run configuration simulation from an already represented frame. The
`3 * n` exact work-step count and `18 * n` compiled-run fuel are measured in source transitions,
not input length; the compiled theorem does not assert `18 * n` successful transitions. It does not
construct a frame from `Tape.ofInput`, prove `boundedDecide`, accept/reject, or `machineOutput`
preservation, decode the interleaved work encoding, normalize or hand off a terminal tape, reset and
launch a second stage, construct a `FunctionProgram.RawRefinement` or
`DecisionProgram.RawRefinement`, compile composition or precomposition, prove an end-to-end
input-size polynomial bound, establish `CNFSAT ∈ P` or NP-completeness, activate the publication
gate, or prove `P = NP`.
