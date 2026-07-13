# Lean executable internal pipeline-output handoff

`lean/PNP/Concrete/PipelineOutputHandoff.lean` defines one literal finite `WorkMachine` for an
already represented pipeline tape. Given a witness that a work tape represents a logical raw tape,
the machine keeps exactly the raw tape's blank-delimited output prefix, installs fresh pipeline
markers around that prefix, returns the head to its first logical cell, and halts accepting. The
endpoint represents the pure target `Tape.handoffTarget raw`, which is
`Tape.ofInput raw.outputBits`.

Discarded logical cells are not erased from the physical tape. They remain beyond the respective
new boundary markers as permitted exterior garbage. The result is therefore an executable internal
re-framing step, not a no-garbage normalization theorem.

## Exact costs

For

```text
n = raw.outputBits.length
```

the exact work-machine trace has

```text
2 * n + 4
```

successful work steps. Compilation expands each work step into six raw steps, so the exact compiled
trace from the encoded internal work configuration has budget

```text
12 * n + 24.
```

This is a bound in the represented source tape's final output length. It is not yet an external
input-size polynomial. A later end-to-end result must separately bound source runtime and tape or
output growth in terms of the original input length.

## Audit

The dedicated transcript prints the axiom closure of every explicit public declaration in the
module:

```bash
lake env lean -DwarningAsError=true lean-audit/PNPConcretePipelineOutputHandoffAxiomAudit.lean
node --test audits/lean-concrete-pipeline-output-handoff0.test.mjs
```

The JavaScript audit closes the public declaration surface, checks the literal finite-rule machine,
requires the exact work and compiled costs, verifies that both endpoints are represented at the
stated logical handoff target, and rejects assumption declarations, proof shortcuts, and broadened
composition or complexity claims. Private proof infrastructure remains excluded from the public
theorem inventory but is still compiled by Lean as part of the module.

## Internal handoff is not terminal raw output

`WorkSymbol` uses two raw tape cells per logical symbol. A logical data bit is followed by its tag
cell in the compiled encoding, and that tag may be a raw blank. Consequently, ordinary raw
`machineOutput` does not in general read a multi-bit represented logical output contiguously. This
module deliberately proves no equality between compiled `machineOutput` and `raw.outputBits`.

The represented endpoint is suitable as an internal logical handoff target. The separate
`TerminalOutputPacker` now proves ordinary raw-machine output semantics from that canonical
represented layout, but no theorem in this module launches the endpoint into it.

## Exact boundary of the result

This module's local compiled trace starts from `encodeWorkConfiguration` of an already represented
internal configuration. `PipelineStageBridges` now launches simulator accept and reject sentinels
into two disjoint copies, preserves the target verdict, and compiles the cumulative supplied exact
trace from ordinary canonical paired `startConfig`.

The resulting endpoint is still the two-track represented `Tape.handoffTarget` in this local
module. `PipelineTerminalBridge` composes it with the terminal packer, and `PipelineCompiler`
places that trace inside an all-input execution with a complete external polynomial for an
already-raw proof-bearing target. There is still no recursive
`FunctionProgram.RawRefinement` or `DecisionProgram.RawRefinement`, `CNFSAT`-in-P result,
NP-completeness result, or `P = NP` consequence.
