# Executable terminal raw-output packer

`lean/PNP/Concrete/TerminalOutputPacker.lean` supplies the literal finite
terminal stage that was missing after the represented-output handoff. It
starts from the canonical two-track representation of a logical bit word,
packs that word into raw-visible work cells, and proves that ordinary
blank-delimited `Tape.outputBits` reads exactly the original word.

This is a stage-local theorem. It has not yet been joined to
`PipelineStageBridges` as one complete pipeline compiler.

## Literal packing machine

The finite rule table scans the represented source word between its boundary
markers. It erases consumed source cells and writes output cells beyond the
old right boundary. The output encoding is:

```text
[]                 -> []
[b]                -> [bitSymbol b]
b0 :: b1 :: suffix -> pairSymbol b0 b1 :: packedSymbols suffix
```

`pairSymbol` covers all four Boolean pairs with `zeroZero`, `zeroOne`,
`oneZero`, and `oneOne`. Under the existing six-transition work-machine
compiler, each packed work symbol exposes its two raw data cells
contiguously. A final `leftMarker` begins with a raw blank and therefore acts
as the observable output delimiter. The theorem is uniform in arbitrary
work-symbol lists outside both original boundary markers.

The empty word takes the direct accepting transition. The universal
two-step induction covers one-bit words, odd and even lengths, all-zero and
all-one words, mixed words, and arbitrary exterior garbage without treating
finite examples as the proof.

## Exact theorem surface

The main declarations are:

- `terminalOutputPacker_workRunExact`: the literal work machine reaches the
  explicit packed accepting configuration in exactly
  `terminalOutputPackerWorkSteps bits` successful transitions;
- `terminalOutputPackerFinal_isHalted`: every such endpoint is the designated
  accepting halt;
- `terminalOutputPacker_output_eq`: ordinary raw blank-delimited observation
  of the encoded final tape equals `bits`;
- `run_compileTerminalOutputPacker_exact`: compilation simulates the exact
  work trace in exactly six raw transitions per work transition;
- `terminalOutputPacker_runtime_le`: the compiled exact trace fits the
  displayed polynomial;
- `run_compileTerminalOutputPacker`: the machine remains at the proved halt
  through the advertised polynomial budget;
- `machineOutput_compileTerminalOutputPacker_eq`: the compiled run's ordinary
  raw output is exactly the logical word; and
- `terminalOutputPacker_one_step_short_timeout`: one work transition less
  than the exact budget is timeout, never an accidental rejection.

The stage starts from an encoded internal work configuration. Its
compatibility-oriented output theorem is not a claim that this machine alone
starts at ordinary external `startConfig`.

## Explicit bounds

For logical output length `n`, the proved work bound is

```text
terminalOutputPackerWorkSteps bits <= n * (3 * n + 5) + n + 1.
```

Compilation costs exactly six raw transitions per successful work
transition. The exported raw polynomial is

```text
terminalOutputPackerRawTimeBound
  = (18 * n * n + 6) + (36 * n + 0)
  = 18*n^2 + 36*n + 6.
```

This is a polynomial in the logical output length for this local stage. It is
not yet a polynomial in the complete pipeline's external encoded input
length, because no theorem here bounds a target machine's runtime or output
length from that external input.

## Audit

```sh
lake build PNP
lake env lean -DwarningAsError=true \
  lean-audit/PNPConcreteTerminalOutputPackerAxiomAudit.lean
node --test audits/lean-concrete-terminal-output-packer0.test.mjs
```

The compiled transcript covers all 69 public declarations and reports an
empty axiom closure for each. The hostile audit fixes the closed import and
declaration surfaces, literal machine and four-way pair encoding, final blank
delimiter, universal exact/halt/output statements, exact polynomial,
one-step-short timeout behavior, nonclaim boundary, and durable root/package/
workflow wiring. Its mutations reject corrupted packing, a changed
delimiter, runtime drift, timeout drift, hidden assumptions, and complexity
overclaims.

## Exact remaining boundary

Terminal raw-output packing is proved as a literal executable stage, and
`PipelineTerminalBridge` now places two verdict-indexed copies in an extended
rule table and proves exact local launches from represented handoff endpoints.
The earlier ordinary-input framer/simulator/handoff trace is still proved for
the smaller bridge machine and has not been transported through that extended
machine. There is therefore no single trace through all four stages, complete
`FunctionProgram.RawRefinement` or `DecisionProgram.RawRefinement`, or
polynomial in external encoded input length. Target termination also remains
an input to the earlier stage-bridge theorem.

Consequently `Formal.ConcreteComplexityMachineLink` remains open,
`PNP.Concrete.cnfSATInP` and `PNP.Concrete.cnfSATNPComplete` remain absent,
`PNP.Main.p_eq_np` remains absent, all seven formal blockers and four project
assumptions remain, and the concrete publication gate remains false.
