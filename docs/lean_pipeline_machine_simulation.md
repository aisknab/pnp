# Lean local framed machine simulation

`lean/PNP/Concrete/PipelineMachineSimulation.lean` is the first executable layer above the
boundary geometry. It translates the ordered rules of one raw `Machine` into a finite
`WorkMachine` that operates on a tape satisfying `PipelineTape.Represents`.

## Exact local result

For one successful source transition

```lean
step? machine raw = some next
```

and any represented work tape, Lean constructs an exact three-transition work run whose final
configuration represents `next`. Interior and stay paths use harmless padding so the cost is
uniform. Empty-side left and right moves shift the corresponding marker across one arbitrary
exterior work symbol; every one of the nine possible exterior symbols is covered.

The existing literal work-machine compiler implements each work transition in exactly six raw
transitions. The compiled corollary therefore runs for exactly eighteen raw transitions from
`encodeWorkConfiguration` and reaches the encoded final work configuration.

## Selection and halting discipline

Raw rule order is preserved. Conflicting duplicate left-hand sides remain legal, and the simulator
uses the same first matching rule as `Machine.findRule`. Source rules whose state is a designated
accept or reject state are omitted because `Machine.step?` checks halting before rule lookup.
Fresh sentinel states separate simulator control from source states and intermediate phases.

A stuck nonhalting raw configuration is not treated as successful or rejecting. The main theorem
requires an actual `some next` source step; malformed data/marker layouts receive no correctness
claim.

## Audit

```bash
lake build PNP
lake env lean -DwarningAsError=true \
  lean-audit/PNPConcretePipelineMachineSimulationAxiomAudit.lean
node --test audits/lean-concrete-pipeline-machine-simulation0.test.mjs
```

The static audit pins the closed imports and complete declaration surface, rejects hidden
assumptions and proof shortcuts, checks ordered first-match construction and terminal-source
suppression, and exercises hostile changes to markers, directions, state separation, and the exact
three/eighteen costs. The dedicated Lean transcript prints the axiom closure of every explicit
declaration.

## Exact nonclaim

This is a one-step configuration simulation from an already encoded frame. It does not construct a
frame from `Tape.ofInput`, decode the interleaved work encoding as `machineOutput`, normalize or
hand off a terminal tape, reset and launch a second stage, lift an arbitrary bounded run, construct
a `FunctionProgram.RawRefinement` or `DecisionProgram.RawRefinement`, compile composition or
precomposition, prove an end-to-end polynomial bound, establish `CNFSAT ∈ P` or NP-completeness,
activate the publication gate, or prove `P = NP`.
