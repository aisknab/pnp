# Uniform canonical-pair pipeline compiler

`lean/PNP/Concrete/PipelinePairedCompiler.lean` closes the supplied-trace and
external-size gaps for proof-bearing target machines on canonical
`BitString.pair` inputs. The executable remains one finite raw `Machine`:

```text
pairedPipelineMachine target
  = compileWorkMachine (PipelineTerminalBridge.terminalBridgeMachine target)
```

There is no host-interpreted stage composition in the theorem statement or
execution path.

## Internally derived target trace

For a target fuel bound `F`,
`PipelineMachineSimulation.rawRunExact?_exists_le_run` extracts a successful
prefix of length `k ≤ F` reaching the same endpoint as the target's ordinary
at-most run. A `PolynomialTimeMachine` supplies the missing termination fact
through `haltsWithin`; the final target verdict therefore selects either the
accepting or rejecting terminal-packer namespace. Timeout is not reclassified
as rejection.

The public correctness theorems are uniform over both pair components:

- `pairedPipeline_boundedDecide_eq` preserves the exact target verdict;
- `pairedPipeline_machineOutput_eq` preserves exact blank-delimited output;
- `pairedPipeline_ne_timeout` proves the compiled run cannot time out; and
- `pairedPipeline_accepts_iff` transfers the target language specification.

All four quantify arbitrary `left right : BitString` and consume an existing
`PolynomialTimeMachine` witness. They do not accept a caller-supplied trace or
proof certificate.

## Output and runtime polynomials

One raw transition can grow the represented output window by at most one
cell. Consequently a target started on an encoded input of length `m` and run
for `p(m)` transitions exposes at most

```text
B(m) = m + p(m) + 1
```

logical output bits. This is `pairedPipelineOutputSizeBound p`.

The complete raw bound is the explicit `NatPolynomial`

```text
R(m) = inputFramerRawTimeBound(m)
     + 6
     + 18 * p(m)
     + 6
     + framedOutputHandoffRawTimeBound(B(m))
     + terminalBridgeRawTimeBound(B(m)).
```

The two output-dependent terms are literal `NatPolynomial.substitute`
expressions. The proof uses the exact six-raw-steps-per-work-step compiler
cost, the exact quadratic framer cost, the two compiled launch costs, the
three-work-steps-per-target-step simulator, and the already proved handoff and
terminal-packer bounds.

## Audit and regressions

```sh
lake build PNP
lake env lean -DwarningAsError=true \
  lean-audit/PNPConcretePipelinePairedCompilerAxiomAudit.lean
lake env lean -DwarningAsError=true \
  lean-regression/PNPConcretePipelinePairedCompiler.lean
node --test audits/lean-concrete-pipeline-paired-compiler0.test.mjs
```

The compiled transcript covers all 28 public declarations and reports an
empty axiom closure for every declaration. The Lean regressions exercise an
empty accepting pair, a mixed nonempty rejecting pair, and general exact
output preservation. The hostile source audit rejects dropped executable
stages, weakened target/output bounds, hidden assumptions, supplied-evidence
shortcuts, output loss, and class/root overclaims.

## Exact remaining boundary

This milestone covers canonical `BitString.pair left right` inputs only. It
does not define exact behavior for empty, odd, malformed, trailing, or other
arbitrary raw bitstrings outside that canonical image. Therefore it is not an
all-bitstring `FunctionProgram.RawRefinement` or
`DecisionProgram.RawRefinement`, and
`Formal.ConcreteComplexityMachineLink` remains open.

`PNP.Concrete.cnfSATInP`, `PNP.Concrete.cnfSATNPComplete`, and
`PNP.Main.p_eq_np` remain absent. All seven formal blockers and four disclosed
project assumptions remain, and the concrete publication gate remains false.
