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

The bounded-run extension starts from an ordinary at-most execution

```lean
run machine F start = final
```

and extracts some exact successful prefix length `k ≤ F` with
`rawRunExact? machine k start = some final`. This extraction applies whether the ordinary run used
all its fuel, halted in a designated state, or stopped because no rule matched. It is a structural
description of the run, not a verdict theorem.

Padding to the full budget is a separate, conditional result. If `final` is designated accept or
reject, then exactly `3 * k` successful work transitions reach a represented halting endpoint.
Because both interpreters leave a designated halt unchanged, `workRun` with fuel
`3 * F` and compiled raw `run` with fuel `18 * F` reach that endpoint and its encoding. The full
`3 * F` and `18 * F` quantities are at-most fuel budgets; they do not say that all those
transitions succeed.

`PipelineInputFramer` now supplies a separate executable trace from literal canonical paired input
to a represented frame. `PipelineStateNamespace` now injectively renames and concatenates the
framer, simulator, and handoff rule tables, proves lookup isolation, and transports this module's
exact traces into the simulation-stage image. That result does not alter this module's premise: no
bridge theorem launches `liftMachine` from the renamed framer accept state, so every simulation
theorem here still begins from an explicitly supplied represented configuration.

## Selection and halting discipline

Raw rule order is preserved. Conflicting duplicate left-hand sides remain legal, and the simulator
uses the same first matching rule as `Machine.findRule`. Source rules whose state is a designated
accept or reject state are omitted because `Machine.step?` checks halting before rule lookup.
Fresh sentinel states separate simulator control from source states and intermediate phases.

A stuck nonhalting raw configuration is not treated as successful, accepting, or rejecting. The
one-step theorem requires an actual `some next` source step, and `rawRunExact?` fails if any of its
`n` requested steps has no successor. Exact-prefix extraction may identify a stuck endpoint, but
the full-fuel padding theorems require that endpoint to be designated halting and therefore do not
promote the stuck endpoint to a verdict. The module proves no termination result and no
`boundedDecide`, timeout, or verdict correspondence. Malformed data/marker layouts receive no
correctness claim.

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
`3 * n` work accounting, exact-prefix extraction, designated-halting guards, and the conditional
`3 * F`/`18 * F` at-most fuel bounds. The dedicated Lean transcript prints the axiom closure of all
96 explicit declarations.

## Exact nonclaim

This is a local configuration simulation from an already represented frame. The exact theorem has
`3 * k` successful work steps for the extracted `k ≤ F`; the padded `3 * F` work fuel and
`18 * F` compiled fuel are at-most budgets measured in source transitions, not input length. The
padding conclusions assume that the supplied `F`-fuel endpoint is designated halting. They do not
prove termination or classify a stuck nonhalting stop as a verdict. This module does not construct a
frame from `Tape.ofInput`; the separate paired-input framer is not composed with it into one
execution even though both now have disjoint images in a concatenated rule table. It does not
prove `boundedDecide`, accept/reject/timeout or `machineOutput`
preservation, decode the interleaved work encoding, connect to the separate internal handoff,
de-tag terminal raw output, reset and launch a second stage, construct a `FunctionProgram.RawRefinement` or
`DecisionProgram.RawRefinement`, compile composition or precomposition, prove an end-to-end
input-size polynomial bound, establish `CNFSAT ∈ P` or NP-completeness, activate the publication
gate, or prove `P = NP`.
