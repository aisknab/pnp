# Lean sequential pipeline compiler

`PNP.Concrete.PipelineSequentialCompiler` compiles two concrete raw machines
into one literal finite raw rule table. Every external bitstring is framed and
run by the first lifted simulator. Either designated first verdict continues:
the represented first output is passed, without host interpretation, to the
second lifted simulator. The second verdict selects its represented handoff
and terminal packer, which emits ordinary blank-delimited raw output.

The public correctness theorem `sequential_correct` proves, for every input,
that the compiled machine has exactly the second bounded execution's verdict
and output. It internally extracts exact prefixes from both bounded runs; no
caller supplies a trace or output-size certificate. The first output bound is

```text
B₁(m) = m + p(m) + 1.
```

The published external runtime polynomial is the conservative composition

```text
R(m) = Ppipeline(p)(m) + 6 + Ppipeline(q)(B₁(m)).
```

It deliberately counts complete single-machine pipeline bounds on both sides
of the inter-component launch, so it safely overcounts the first terminal
packer and the second input framer that the literal sequential execution
skips. The exact executed work cost is separately exposed by
`sequentialWorkSteps` and `sequentialRawSteps`.

Accept/accept, reject/accept, accept/reject, arbitrary-output, empty/odd input,
and stuck-first-machine regressions are compiled. A stuck nonhalting first
endpoint remains timeout and cannot be reclassified as rejection.

This milestone does not yet define recursive `FunctionProgram.RawRefinement`
or `DecisionProgram.RawRefinement` constructors, so the concrete complexity
machine-link blocker remains open. It does not prove CNFSAT in P,
NP-completeness, or P = NP. The publication gate remains false.

```bash
lake build PNP
lake env lean -DwarningAsError=true \
  lean-audit/PNPConcretePipelineSequentialCompilerAxiomAudit.lean
lake env lean -DwarningAsError=true \
  lean-regression/PNPConcretePipelineSequentialCompiler.lean
node --test audits/lean-concrete-pipeline-sequential-compiler0.test.mjs
```
