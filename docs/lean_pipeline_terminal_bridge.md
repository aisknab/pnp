# Executable handoff-to-terminal bridge

`lean/PNP/Concrete/PipelineTerminalBridge.lean` extends the literal stage
bridge rule table with two verdict-indexed copies of
`TerminalOutputPacker`. From an already reached accepting or rejecting
represented-handoff endpoint, it proves one exact launch followed by the
complete terminal-packing trace. It also proves that every successful step
and exact trace in the earlier bridge machine is preserved without shadowing
in the extended table. For a caller-supplied exact accepting or rejecting
target execution, these results compose into one exact trace from ordinary
paired input through all four stages of the literal finite machine.

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

## Exact local and supplied traces

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

`bridged_workStep?_of_some` and `bridged_workRunExact_of_exact` transport the
earlier bridge rules into the extended machine. The two theorems

- `acceptingSuppliedTrace_workRunExact_of_rawRunExact`; and
- `rejectingSuppliedTrace_workRunExact_of_rawRunExact`

then compose framing, lifted simulation, represented handoff, terminal
launch, and terminal packing from ordinary `BitString.pair` input. Their
premise is a supplied `rawRunExact?` target execution with an accepting or
rejecting endpoint. They do not prove that such an execution exists for every
input.

At the same exact cumulative budget,
`workBoundedDecide_terminalBridge_accept_of_rawRunExact` and its rejecting
counterpart preserve the target verdict. A supplied stuck nonhalting endpoint
remains `.timeout` at the exact simulation-prefix budget. The two
`machineOutput_compileTerminalBridge_*_of_rawRunExact` theorems prove that
ordinary raw-machine output is exactly the supplied target final tape's
logical output.

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
is not a polynomial in the complete pipeline's external encoded input length.
For a supplied exact target trace, the total work cost is

```text
inputFramerWorkSteps (packedPairCount left right)
  + 1
  + 3 * sourceSteps
  + 1
  + framedOutputHandoffWorkSteps finalTape
  + 1
  + terminalOutputPackerWorkSteps finalTape.outputBits
```

and the compiled raw cost is exactly six times that sum. Target termination,
a source runtime polynomial in external input size, and final-output-size
transport remain unproved.

## Audit

```sh
lake build PNP
lake env lean -DwarningAsError=true \
  lean-audit/PNPConcretePipelineTerminalBridgeAxiomAudit.lean
node --test audits/lean-concrete-pipeline-terminal-bridge0.test.mjs
```

The compiled transcript covers all 59 public declarations and reports an
empty axiom closure for every declaration. The hostile audit fixes the closed
import and declaration surfaces, disjoint state images, literal rule order,
first-match lookup isolation, preservation of all successful earlier steps,
both supplied verdict-indexed traces, final halts, exact raw output, timeout
behavior, the cumulative cost, the local polynomial, and the explicit
nonclaim boundary. Mutations reject namespace collapse, missing prior rules,
bound drift, output drift, hidden assumptions, and class/root overclaims.

## Exact remaining boundary

The complete literal trace theorem requires a caller-supplied exact target
execution. No theorem supplies target termination, a uniform all-input
`FunctionProgram.RawRefinement` or `DecisionProgram.RawRefinement`, or a
polynomial in external encoded input length.

`Formal.ConcreteComplexityMachineLink` remains open;
`PNP.Concrete.cnfSATInP`, `PNP.Concrete.cnfSATNPComplete`, and
`PNP.Main.p_eq_np` remain absent; all seven formal blockers and four project
assumptions remain; and the concrete publication gate remains false.
