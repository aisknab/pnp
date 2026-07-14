# Lean all-input four-stage pipeline compiler

`lean/PNP/Concrete/PipelineCompiler.lean` proves the complete literal raw
pipeline correct for every `BitString` input to an already-raw proof-bearing
target. It uses exactly the same executable rule table as
`PipelinePairedCompiler`:

```lean
def PNP.Concrete.PipelineCompiler.pipelineMachine
    (target : Machine) : Machine :=
  compileWorkMachine (PipelineTerminalBridge.terminalBridgeMachine target)
```

There is no host-interpreted stage composition. The finite work table contains
the total input framer, renamed target simulator, two represented-output
handoff copies, and two terminal raw-output packer copies. The result covers
empty, odd, even, malformed, and otherwise non-pair raw words uniformly.

## Exact result

For `target : PolynomialTimeMachine language` and every `input : BitString`,
the public interface proves:

- `pipeline_boundedDecide_eq`: the compiled verdict equals the target verdict;
- `pipeline_machineOutput_eq`: ordinary first-blank-delimited raw output is
  identical;
- `pipeline_ne_timeout`: the compiled machine does not time out at its stated
  bound;
- `pipeline_accepts_iff`: compiled acceptance is equivalent to `language input`;
- `toPolynomialTimeMachine`: the compiled raw machine is another
  `PolynomialTimeMachine language`.

The underlying `pipeline_correct` theorem assumes only the target's advertised
bounded termination for that input. It obtains an exact successful target
prefix internally from the ordinary bounded run; callers do not provide a
certificate or execution trace.

The separate supplied-trace lemmas remain useful for exact accounting. A
target execution of exactly `n` raw steps is lifted to exactly `3*n` simulator
work steps. The two launch transitions cost six compiled raw steps each. A
stuck endpoint that is neither accept nor reject remains `timeout` at the
simulation-prefix budget; it is never reclassified as rejection.

## External polynomials

If the target time polynomial is `p`, the compiler uses the output bound

```text
B(m) = m + p(m) + 1
```

and the raw runtime polynomial

```text
R(m) = totalInputFramerRawTimeBound(m)
     + 6
     + 18*p(m)
     + 6
     + framedOutputHandoffRawTimeBound(B(m))
     + terminalBridgeRawTimeBound(B(m)).
```

The total-framer term is bounded by `6*m*m + 39*m + 75`. The handoff and
terminal terms are polynomial substitutions at `B(m)`, so the complete bound
depends only on external encoded input length. The output-length theorem uses
the same `B(m)`.

## Ordinary-start connection

The work compiler materializes additional exterior blank cells. The theorem
does not identify finite tape lists syntactically. It uses
`Configuration.BlankEquivalent`, `run_blankEquivalent`, and
`Tape.outputBits_eq_of_blankEquivalent` to prove that the ordinary raw
`startConfig` and the encoded work start have the same run behavior and
observable output.

## Audit and regression surface

The dedicated kernel transcript covers all 29 explicit public declarations:

```bash
lake build PNP
lake env lean -DwarningAsError=true \
  lean-audit/PNPConcretePipelineCompilerAxiomAudit.lean
lake env lean -DwarningAsError=true \
  lean-regression/PNPConcretePipelineCompiler.lean
node --test audits/lean-concrete-pipeline-compiler0.test.mjs
```

Every printed axiom closure is empty. The Lean regression covers empty input,
an odd one-bit input, arbitrary output preservation, the canonical-pair
compatibility route, and a concrete stuck-machine timeout. The hostile static
audit rejects narrowed pair-only input, weakened costs or output bounds,
caller-supplied evidence, assumptions, SAT/oracle shortcuts, and claim
activation.

## Exact remaining boundary

This compiler wraps one already-raw `PolynomialTimeMachine`.
`PipelineSequentialCompiler` composes two such wrappers, and
`PipelineRefinement` recursively uses that construction for every
`FunctionProgram.compose` and `DecisionProgram.precompose` node. Consequently
`Formal.ConcreteComplexityMachineLink` is now discharged.

It does not prove `PNP.Concrete.cnfSATInP`,
`PNP.Concrete.cnfSATNPComplete`, or `PNP.Main.p_eq_np`. Four disclosed project
assumptions and six formal blockers remain. The concrete publication
gate remains false, so the repository does not establish `P = NP`.
