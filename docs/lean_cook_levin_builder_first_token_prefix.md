# Composed Cook–Levin builder first-token prefix

`lean/PNP/Concrete/CookLevinBuilderFirstTokenPrefix.lean` defines one literal
finite work machine that starts from an ordinary raw bitstring, runs the total
input framer and unary length tally, launches the token appender, and emits the
first canonical `T` header token.

## Literal 184-rule composition

The two complete component machines are renamed through injective, disjoint
outer state maps:

```text
prefixState   = inputState
appenderState = simulationState
```

Nine symbol-preserving bridge rules connect only the renamed input-prefix
accept state to the renamed appender start state. The bridge comes first in
the literal table:

```lean
launchRules ++
  (BuilderInputPrefix.machine.rules.map (renameRule prefixState) ++
   BuilderTokenAppender.machine.rules.map (renameRule appenderState))
```

This is exactly `9 + 116 + 59 = 184` rules. The queries are pairwise distinct,
and first-match lookup transports every successful component rule into its
renamed image. Only the appender's renamed accept and reject states are global
halts, so the completed prefix endpoint must take the bridge before the
composed machine can accept.

## Exact all-input trace

For every raw `BitString input`, the exact work cost is defined by composition:

```lean
BuilderInputPrefix.workSteps input + 1 +
  BuilderTokenAppender.workSteps input []
```

`prefix_workRunExact` transports the complete framer/tally trace,
`launch_workStep` proves the tape- and head-preserving bridge transition, and
`appender_workRunExact` transports the first-token trace. `workRunExact`
composes all three pieces from `rawInputWorkTape input` to the sole accepting
endpoint.

The final workspace preserves the represented source word and exact unary
tally and contains output `[CNFToken.t]`. Lean proves both
`finalTape_represents` and:

```lean
CNFToken.t.bits = problem.encodedFormula.take 2
```

for every concrete verifier-tableau problem. Thus this machine emits exactly
the first two canonical formula bits; the token is fixed and independent of
the verifier's answer.

## Compiled external bound

The reviewed raw bound is the input-prefix bound, six raw transitions for the
new work-level launch, and the appender's first-token bound:

```text
18*n^2 + 63*n + 93 + 6 + 24*n + 48
  = 18*n^2 + 87*n + 147
```

`run_compile_exact` proves the exact six-for-one compiled trace.
`run_compile_rawTimeBound` and
`run_compile_rawTimeBound_blankEquivalent` prove the displayed external bound
for canonical and blank-equivalent raw tapes. At that fuel,
`boundedDecide_compile_accept` returns `accept` and
`boundedDecide_compile_ne_timeout` excludes timeout.

## Fail-closed cases and audit

The following cases remain timeout rather than being promoted to a verdict:

- the exact prefix endpoint when fuel ends before the bridge;
- the prefix's malformed tally phase;
- the appender's malformed tally and output phases; and
- the ordinary raw-input run with one successful work transition removed.

Regression cases cover empty input, one-bit zero and one, odd and even lengths,
all-zero and all-one words, the exact bridge, exact final tape and token,
polynomial evaluation, disjoint state images, a prefix reject/stuck state, and
all malformed or short-fuel boundaries. The hostile audit removes or shadows
the bridge, collides the state maps, changes the rule count, bound, token, or
formula bits, weakens timeout claims, and injects forbidden assumptions or
host-level shortcuts; every mutation must be rejected.

The module exposes 37 declarations. Its compiled axiom audit reports 21 with
empty closure, three using only `propext`, and 13 using only `propext` plus
`Quot.sound`. No public declaration reaches a project axiom,
`Classical.choice`, `sorryAx`, a SAT/minimization oracle, host composition, or a
caller-supplied certificate.

Run:

```bash
lake build PNP
lake env lean -DwarningAsError=true \
  lean-audit/PNPConcreteCookLevinBuilderFirstTokenPrefixAxiomAudit.lean
lake env lean -DwarningAsError=true \
  lean-regression/PNPConcreteCookLevinBuilderFirstTokenPrefix.lean
node --test \
  audits/lean-concrete-cook-levin-builder-first-token-prefix0.test.mjs
```

## Exact nonclaim

This milestone emits only the fixed first `T` token. It does not compute the
rest of the unary width header, implement a dynamic formula cursor, emit the
complete formula, construct a builder `RawRefinement`, package a concrete
`PolynomialReduction`, prove CNFSAT NP-hard or NP-complete, prove CNFSAT in P,
or prove `P = NP`. `PNP.Main.p_eq_np` remains absent and the publication gate
remains false.
