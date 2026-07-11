# Lean executable paired-input framer

`lean/PNP/Concrete/PipelineInputFramer.lean` defines one literal finite `WorkMachine` that consumes
the canonical packed representation of `BitString.pair left right`. The existing work-input bridge
turns the compiled raw machine's `startConfig` into the packed work tape used by the framer proof.
The machine installs a separate outer sentinel cell using `PipelineTape.rightMarker`, consumes the
packed source cells one at a time,
copies their two component bits into fresh `PipelineTape.dataSymbol` cells, installs the left and
right markers, returns the head to the first copied data cell, and halts in its accepting state.

The endpoint is a valid `PipelineTape.Represents` frame for
`Tape.ofInput (BitString.pair left right)`. The consumed source region is blanked but remains to the
left of the outer sentinel. That region is deliberately recorded as `outsideLeft` garbage; the
representation relation permits it, so this is not a no-garbage normalization result.

## Exact costs

For

```text
k = left.length + right.length + 1
m = (BitString.pair left right).length = 2 * k
```

the exact work-machine trace has

```text
4 * k * k + 9 * k + 7
```

successful work steps. Compilation expands each work step into six raw steps, giving the exact raw
budget

```text
24 * k * k + 54 * k + 42
  = 6 * m * m + 27 * m + 42.
```

The exported `NatPolynomial` records the latter raw-input-length expression. The public compiled
endpoint theorem begins with the literal canonical raw configuration

```lean
startConfig (compileWorkMachine pairedInputFramer) (BitString.pair left right)
```

and reaches the encoding of the represented accepting endpoint at that polynomial fuel.

## Audit

The dedicated transcript prints the axiom closure of every explicit public declaration in the module:

```bash
lake env lean -DwarningAsError=true lean-audit/PNPConcretePipelineInputFramerAxiomAudit.lean
node --test audits/lean-concrete-pipeline-input-framer0.test.mjs
```

The JavaScript audit closes the public declaration surface, checks the literal finite-rule and
canonical-input structure, rejects Lean assumption declarations and proof shortcuts, requires the
exact work/raw cost formulas, and verifies that the transcript covers every public head exactly
once. Private proof infrastructure remains excluded from the public theorem inventory but is still
compiled by Lean as part of the module.

## Exact boundary of the result

This is a paired-input framer only. Every input in its public theorem has the form
`BitString.pair left right`, whose raw length is positive and even. There is no theorem for an
arbitrary empty, odd, malformed, or otherwise unpaired raw bitstring.

The accepting framer is not yet composed with `PipelineMachineSimulation.liftMachine`. In
particular, this layer does not merge their rule lists, allocate disjoint control states, retag the
framer's accepting state as a simulated machine's start state, launch the simulator, establish a
`FunctionProgram.RawRefinement` or `DecisionProgram.RawRefinement`, or derive an end-to-end input
size bound. Its local `boundedDecide` theorem says only that the framer accepts at its proved
budget. It does not prove target-machine termination, simulated-stage `boundedDecide`
correspondence, target accept/reject/timeout preservation, output decoding, connection to the
separate internal represented-output handoff, terminal raw output de-tagging,
`CNFSAT ∈ P`, NP-completeness, or `P = NP`.
