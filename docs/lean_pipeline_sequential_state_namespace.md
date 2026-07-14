# Lean sequential pipeline state namespace

`PNP.Concrete.PipelineSequentialStateNamespace` places two complete, already
audited work-pipeline components in disjoint outer control-state images.  The
first component contains the all-input framer, first lifted simulator, and
represented-output handoff.  The second contains the second lifted simulator,
its verdict-indexed handoffs, and terminal output packers.

The literal combined rule table adds two symbol-preserving launches.  Both the
accepting and rejecting first-component handoff endpoints launch the same
second simulator start.  This is required for function composition: a first
machine's designated verdict does not suppress its output or decide the final
verdict.  Only the second component's terminal packer copies are global halts.

The module proves injectivity and disjointness of the outer state images,
first-match lookup isolation, preservation of every successful local step and
exact local trace, and exact accept/reject launches into the second simulator.
The component tables are renamed and concatenated as finite `WorkRule` lists;
there is no host-interpreted execution or rule dispatch.

This module is an isolation milestone only. Downstream modules now compose the
end-to-end two-machine trace, provide an external input-size polynomial, define
recursive `RawRefinement`, and close `Formal.ConcreteComplexityMachineLink`.
They do not prove CNFSAT in P or NP-complete, or establish P = NP. The
publication gate remains false.

The kernel and hostile-source checks are:

```bash
lake build PNP
lake env lean -DwarningAsError=true \
  lean-audit/PNPConcretePipelineSequentialStateNamespaceAxiomAudit.lean
node --test audits/lean-concrete-pipeline-sequential-state-namespace0.test.mjs
```
