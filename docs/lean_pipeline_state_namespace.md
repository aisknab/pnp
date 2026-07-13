# Lean collision-free pipeline state namespace

`lean/PNP/Concrete/PipelineStateNamespace.lean` is the first literal
rule-table composition layer above the previously separate input framer,
framed simulator, and represented-output handoff.

## Injective work-machine renaming

The module defines finite state renaming for `WorkRule`,
`WorkConfiguration`, and `WorkMachine`.  For every injective map on natural
states, Lean proves that renaming preserves:

- ordered first-match `findWorkRule` selection;
- designated halt status;
- rule application and one-step execution;
- ordinary fuel-bounded execution;
- exact successful execution; and
- the `accept` / `reject` / `timeout` result of `workBoundedDecide`.

The theorem `findWorkRule_rename` is order-sensitive: duplicate left-hand
sides remain legal, and the renamed table selects the renamed copy of the
same first source rule.  No rule sorting or deduplication is performed.

## Three disjoint stage images

The finite tag type is:

```lean
inductive Stage where
  | input
  | simulation
  | handoff
```

`stageState payload stage` uses a three-way recursive encoding.  Lean proves
that equality of encoded states implies equality of both the payload and the
stage tag.  Consequently `inputState`, `simulationState`, and `handoffState`
are individually injective and pairwise disjoint.

`composedRules input simulation handoff` is a literal concatenation of the
three renamed finite rule lists.  The three lookup-isolation theorems prove
that a query in one stage image sees exactly that stage's first matching rule
and cannot be captured by either other stage's table.  This closes the
state-collision and rule-order prerequisite for a later composed machine.

## Existing exact traces survive renaming

The module instantiates the calculus for the existing machines and proves:

- the canonical paired-input framer retains its exact quadratic work trace in
  the input image;
- every supplied exact raw run retains the simulator's exact `3 * n` work
  trace in the simulation image; and
- the represented-output handoff retains its exact `2 * n + 4` work trace in
  the handoff image.

These are the same stage-local executions under injective renaming.  They do
not yet form one execution.

## Audit

```bash
lake build PNP
lake env lean -DwarningAsError=true \
  lean-audit/PNPConcretePipelineStateNamespaceAxiomAudit.lean
node --test audits/lean-concrete-pipeline-state-namespace0.test.mjs
```

The Lean transcript covers all 39 explicit public declarations and reports an
empty axiom closure for each.  The hostile static audit closes the import and
declaration surfaces, checks the exact three-way encoding and concatenation,
requires all three lookup-isolation theorems and stage-local trace transports,
and rejects state collisions, missing stages, assumptions, proof shortcuts,
or broadened complexity claims.

## Exact nonclaim

This namespace module itself supplies no bridge transition. The subsequent
`PipelineStageBridges` module uses these disjoint images to prove the exact
framer-to-simulator and simulator-to-verdict-indexed-handoff launches and one
cumulative internal execution. `PipelineTerminalBridge` adds the fourth
terminal-packer stage, and `PipelineCompiler` proves the complete literal table
correct for every raw input with an external polynomial. There is still no
recursive `FunctionProgram.RawRefinement` or `DecisionProgram.RawRefinement`,
`CNFSAT ∈ P`, NP-completeness, or `P = NP`. The
`Formal.ConcreteComplexityMachineLink` blocker remains active.
