# Executable Cook–Levin builder input prefix

`lean/PNP/Concrete/CookLevinBuilderInputPrefix.lean` composes the existing
all-input framer and fixed 19-rule unary input-length tally inside one literal
finite work machine. This is the first builder prefix that starts from an
ordinary raw `BitString`; it is not a formula builder.

## Literal machine

The module reuses two previously audited injective state images:

```lean
framerState state = PipelineStateNamespace.inputState state
tallyState state  = PipelineStateNamespace.simulationState state
```

Their images are pairwise disjoint. The global rule table is literally:

```lean
launchRules ++
  pairedInputFramer.rules.map (renameRule framerState) ++
  BuilderInputLength.machine.rules.map (renameRule tallyState)
```

`launchRules` contains one symbol- and head-preserving transition for each of
the nine `WorkSymbol` values. It sends the renamed framer accept state to the
renamed tally start state. Bridge-first ordering is proved harmless away from
that exact source state, and the two renamed stage tables cannot shadow each
other. Only the renamed tally accept and reject states are global halts.

## Exact execution

For every raw input, the cumulative work cost is:

```text
totalInputFramerWorkSteps(input)
+ 1
+ (2*n*n + 4*n + 2)
```

where `n = BitString.size input = input.length`. The principal theorem is:

```lean
PNP.Concrete.CookLevin.BuilderInputPrefix.workRunExact
  (input : BitString) :
  workRunExact? machine (workSteps input)
      (workStartConfiguration machine (rawInputWorkTape input)) =
    some (finalConfiguration input)
```

The final tape is exactly the existing tally endpoint with the framer's
proved exterior-left region. The source bits remain represented and the fresh
right workspace contains exactly `n` unary tally symbols.

The ordinary work-machine compiler uses six raw transitions for each proved
work transition. Combining the existing framer bound, six bridge transitions,
and the exact tally cost gives the all-input polynomial:

```text
(6*n*n + 39*n + 75)
+ 6
+ (12*n*n + 24*n + 12)
= 18*n*n + 63*n + 93
```

`run_compile_exact` proves the exact six-for-one trace.
`run_compile_rawTimeBound` proves the padded polynomial-budget endpoint, and
`run_compile_rawTimeBound_blankEquivalent` connects it to ordinary raw
`startConfig`. Therefore `boundedDecide_compile_accept` and
`boundedDecide_compile_ne_timeout` hold for every `BitString`. Acceptance here
means only that input preparation completed; it is not a language decision.

## Fail-closed behavior

- the framer's local accept state is globally nonhalting and must take the
  explicit launch;
- malformed tally scan configurations whose head is `WorkSymbol.zeroOne`
  have no matching rule, remain nonhalting for every fuel value, and therefore
  time out;
- removing exactly one work transition from the complete successful trace
  leaves a nonhalting state and reports timeout;
- first-match lookup theorems prove that neither renamed stage falls through
  into the other table.

## Audit and regression boundary

The module exposes 40 declarations. The complete compiled axiom transcript
records 29 declarations with empty closure, one using only `propext`, and ten
using only `propext` and `Quot.sound`. No declaration reaches a project axiom,
`Classical.choice`, or `sorryAx`.

The regression file covers empty, one-bit, odd, even, all-zero, all-one, and
mixed inputs; exact work and raw costs; exact final tapes; launch execution;
compiled execution; the polynomial budget; the unused `zeroOne` scan symbol;
and
one-step-short timeout. The hostile audit mutates state images, bridge order
and target, endpoint construction, polynomial coefficients, timeout fuel,
assumptions, and theorem scope and requires every mutation to fail closed.

Run:

```bash
lake build PNP
lake env lean -DwarningAsError=true \
  lean-audit/PNPConcreteCookLevinBuilderInputPrefixAxiomAudit.lean
lake env lean -DwarningAsError=true \
  lean-regression/PNPConcreteCookLevinBuilderInputPrefix.lean
node --test \
  audits/lean-concrete-cook-levin-builder-input-prefix0.test.mjs
```

## Exact nonclaim

This milestone emits no formula bit, interprets no direct cursor coordinate as
raw execution, and does not compose the remaining formula-emission stages. It
provides no complete builder, construction-runtime `RawRefinement`, concrete
`PolynomialReduction`, CNFSAT NP-hardness or NP-completeness, CNFSAT-in-P
theorem, or P-equals-NP theorem. `PNP.Main.p_eq_np` remains absent and the
publication gate remains false.
