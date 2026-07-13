# Executable pipeline stage bridges

`lean/PNP/Concrete/PipelineStageBridges.lean` turns the collision-free state
namespace into one literal finite work machine with explicit stage launches.
It is an internal-output execution theorem, not the finished pipeline
compiler.

## Finite control layout

The framer and simulator retain the disjoint `inputState` and
`simulationState` images proved in `PipelineStateNamespace`. The handoff image
is split once more:

```text
acceptingHandoffState q = handoffState (inputState q)
rejectingHandoffState q = handoffState (simulationState q)
```

Both maps are injective and their images are disjoint. The global accepting
halt is the local handoff accept state in the first image; the global
rejecting halt is the same local handoff accept state in the second image.
Thus output handoff does not erase the target machine's verdict.

Each launch table contains exactly one symbol-preserving `.stay` rule for
each of the nine `WorkSymbol` values. The bridge-first finite rule list is:

```text
framer-accept launch
accept-sentinel launch
reject-sentinel launch
renamed framer rules
renamed simulator rules
accepting handoff-copy rules
rejecting handoff-copy rules
```

The first-match isolation theorems prove that bridge priority cannot capture
an ordinary successful framer, simulator, or handoff step. The three launch
theorems prove the exact one-step endpoints:

- `inputLaunch_workStep`
- `acceptingLaunch_workStep`
- `rejectingLaunch_workStep`

## Cumulative exact traces

For canonical paired input `left.pair right`, a supplied exact target run of
`n` raw transitions, and target final tape `t`, the internal work cost is

```text
inputFramerWorkSteps (packedPairCount left right)
  + 1
  + 3 * n
  + 1
  + framedOutputHandoffWorkSteps t
```

where the already-proved handoff term is
`2 * t.outputBits.size + 4`. Compilation uses exactly six raw transitions per
work transition, so `bridgedRawSteps` is six times the displayed sum. These
costs depend on a supplied exact source-transition count and final output
length; they are not yet a polynomial in external encoded input length.

`bridgedAccept_workRunExact_of_rawRunExact` and
`bridgedReject_workRunExact_of_rawRunExact` compose the framer, both launch
steps, the three-for-one simulator, and the selected handoff copy. The
corresponding `workBoundedDecide` theorems preserve target acceptance and
rejection. `workBoundedDecide_bridged_timeout_of_stuck_rawRunExact` records
that a supplied stuck nonhalting endpoint remains timeout at the exact
simulation-prefix budget rather than being promoted to rejection.

The compiled theorems
`run_compileBridgedMachine_accept_of_rawRunExact` and
`run_compileBridgedMachine_reject_of_rawRunExact` begin at ordinary raw
`startConfig` on the canonical paired input and reach the encoded internal
handoff endpoint at `bridgedRawSteps`.

## Audit

```sh
lake build PNP
lake env lean -DwarningAsError=true \
  lean-audit/PNPConcretePipelineStageBridgesAxiomAudit.lean
node --test audits/lean-concrete-pipeline-stage-bridges0.test.mjs
```

The Lean transcript covers all 56 public declarations and reports an empty
axiom closure for each. The hostile audit fixes the declaration surface,
finite bridge order, verdict split, exact work/raw costs, nonclaim boundary,
and required root/workflow wiring; its mutations reject verdict collapse,
missing or reordered launches, altered costs, hidden assumptions, and class
overclaims.

## Exact remaining boundary

The handoff endpoint of this module is still a two-track represented work
tape. `PipelineTerminalBridge` now extends this rule table with two terminal-
packer copies, preserves every successful earlier bridge step in the extended
table, and composes the local accepting and rejecting suffixes. For every
caller-supplied exact accepting or rejecting target execution, the terminal
module proves one four-stage exact trace from ordinary paired input.
`PipelineCompiler` now supplies target termination, every-raw-input behavior,
and a polynomial in external encoded input length for an already-raw
`PolynomialTimeMachine`. It does not supply recursive
`FunctionProgram.RawRefinement` or `DecisionProgram.RawRefinement`, `CNFSAT ∈ P`,
CNFSAT NP-completeness, or `P = NP`.

`Formal.ConcreteComplexityMachineLink` therefore remains active,
`PNP.Main.p_eq_np` remains absent, and the publication gate remains false.
