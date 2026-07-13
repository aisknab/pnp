# Executable handoff-to-terminal bridge

`lean/PNP/Concrete/PipelineTerminalBridge.lean` extends the literal stage
bridge rule table with two verdict-indexed copies of
`TerminalOutputPacker`. From an already reached accepting or rejecting
represented-handoff endpoint, it proves one exact launch followed by the
complete terminal-packing trace.

This is a local suffix theorem. The earlier trace from ordinary paired input
is proved for `PipelineStageBridges.bridgedMachine`; it has not yet been
transported through the extended machine in this module.

## Finite namespace and rule table

The two packer copies use nested injective state images:

```text
acceptingPackerState q = handoffState (acceptingHandoffState q)
rejectingPackerState q = handoffState (rejectingHandoffState q)
```

Lean proves both maps injective, their images pairwise disjoint, and both
images disjoint from the accepting and rejecting handoff images. The literal
finite table is ordered as:

```text
accepting handoff-to-packer launch
rejecting handoff-to-packer launch
all prior PipelineStageBridges rules
renamed accepting terminal-packer rules
renamed rejecting terminal-packer rules
```

`findWorkRule_terminalBridge_acceptingPacker_of_some` and its rejecting
counterpart prove first-match isolation: every successful local packer lookup
is the corresponding renamed lookup in the combined table. The two launch
tables contain one symbol-preserving `.stay` rule for each `WorkSymbol`.

## Exact local traces

For any `PipelineTape.Represents raw.handoffTarget work`, the representation
witness exposes arbitrary exterior garbage around the canonical packer input.
The theorems

- `acceptingTerminal_workRunExact_of_represents`; and
- `rejectingTerminal_workRunExact_of_represents`

compose exactly one launch with the complete local packer run. Their final
states are distinct designated accepting and rejecting halts of
`terminalBridgeMachine`. The compiled exact-trace theorems use six raw
transitions per work transition, while the padded variants remain at the
same halt through the advertised local polynomial budget.

At that budget,
`outputBits_compileTerminalBridge_accepting_of_represents` and
`outputBits_compileTerminalBridge_rejecting_of_represents` prove that ordinary
blank-delimited `Tape.outputBits` equals `raw.outputBits`. The rejecting copy
preserves the output while retaining the rejecting control-state image.

## Explicit local polynomial

For logical output length `n`, the exact local suffix cost is

```text
terminalBridgeWorkSteps bits
  = 1 + terminalOutputPackerWorkSteps bits

terminalBridgeRawSteps bits
  = 6 * terminalBridgeWorkSteps bits.
```

The proved conservative raw polynomial adds six compiled transitions for the
launch to the packer's existing bound:

```text
terminalBridgeRawTimeBound
  = terminalOutputPackerRawTimeBound + 6
  = 18*n^2 + 36*n + 12.
```

This polynomial is in logical output length at the represented endpoint. It
is not a polynomial in the complete pipeline's external encoded input length,
because target termination, source runtime, and output-size transport into
this extended machine remain unproved.

## Audit

```sh
lake build PNP
lake env lean -DwarningAsError=true \
  lean-audit/PNPConcretePipelineTerminalBridgeAxiomAudit.lean
node --test audits/lean-concrete-pipeline-terminal-bridge0.test.mjs
```

The compiled transcript covers all 44 public declarations and reports an
empty axiom closure for every declaration. The hostile audit fixes the closed
import and declaration surfaces, disjoint state images, literal rule order,
first-match lookup isolation, both exact launches, both verdict-indexed
traces, final halts, raw output equality, the local polynomial, and the
explicit nonclaim boundary. Mutations reject namespace collapse, missing
prior rules, bound drift, output drift, hidden assumptions, and class/root
overclaims.

## Exact remaining boundary

There is still no theorem transporting the earlier framer, simulator, and
handoff trace from ordinary paired `startConfig` into
`terminalBridgeMachine`. Consequently there is no single four-stage exact
trace, no complete `FunctionProgram.RawRefinement` or
`DecisionProgram.RawRefinement`, no external encoded-input-size polynomial,
and no target-termination result.

`Formal.ConcreteComplexityMachineLink` remains open;
`PNP.Concrete.cnfSATInP`, `PNP.Concrete.cnfSATNPComplete`, and
`PNP.Main.p_eq_np` remain absent; all seven formal blockers and four project
assumptions remain; and the concrete publication gate remains false.
