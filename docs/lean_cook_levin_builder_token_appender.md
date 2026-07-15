# Standalone Cook–Levin builder token appender

`lean/PNP/Concrete/CookLevinBuilderTokenAppender.lean` formalizes the next
bounded builder component: one fixed finite work machine that appends exactly
one state-selected canonical CNF token after the unary input-length tally. It
is deliberately standalone. Its rule table is not yet concatenated with the
executable input prefix.

## Literal token and state encoding

The four token requests have fixed codes and pairwise-distinct work symbols:

```text
F         state code 0   work symbol zeroZero   raw bits 00
T         state code 1   work symbol oneOne     raw bits 11
separator state code 2   work symbol zeroOne    raw bits 01
finish    state code 3   work symbol oneZero    raw bits 10
```

The request is carried only by the finite control state. The machine allocates
three four-state scan phases, three shared rewind states, and distinct accept
and reject states. Its literal table is:

```lean
allTokens.flatMap tokenRules ++ rewindRules
```

There are exactly 59 rules and their `(sourceState, readSymbol)` queries are
pairwise distinct. Neither the rule table nor the machine definition accepts a
source input, formula, answer bit, schedule, certificate, SAT result, or
minimization result as executable program data.

## Workspace and exact execution

The work tape preserves the represented raw input, then stores the proved
unary length tally, a phase-local output delimiter, and zero or more complete
token symbols. For an empty prior token list the delimiter is not yet
materialized, so the start tape is definitionally the existing
`BuilderInputLength.finalTape` endpoint.

For source word `input`, arbitrary exterior-left cells `outsideLeft`, prior
canonical token list `output`, and any request `request`, the main theorem is:

```lean
PNP.Concrete.CookLevin.BuilderTokenAppender.appendToken_workRunExact
  (input : BitString) (outsideLeft : List WorkSymbol)
  (output : List CNFToken) (request : CNFToken) :
  workRunExact? machine (workSteps input output)
      (entryConfiguration request
        (workspaceTape input outsideLeft output)) =
    some (finalConfiguration input outsideLeft (output ++ [request]))
```

Writing `n = input.length` and `k = output.length`, the exact work cost is:

```text
2 * (max 1 n + n + k + 3)
```

The forward pass scans the materialized source word, the exact `n`-cell tally,
and the existing `k` tokens before writing the selected token. The reverse
pass crosses the same regions and restores the logical input focus. The proof
is uniform in all four requests, every input length, every prior token list,
and arbitrary exterior garbage.

## First canonical formula token

The machine start state requests `CNFToken.t`. From a supplied tally endpoint,
`firstHeaderToken_workRunExact` therefore appends the first header token.
`firstHeaderToken_after_builderInputPrefix` specializes the supplied tape to
the endpoint established by the separate input-prefix theorem; it is not a
rule-table composition theorem.

The compiler uses six raw transitions per work transition. For the first
token, Lean proves the external encoded-input-size bound:

```text
6 * workSteps input [] <= 24 * input.length + 48
```

`run_compile_firstHeaderToken_rawTimeBound` reaches the encoded endpoint at
that budget. The bound covers the materialized blank source cell for empty
input without treating a bounded example as the universal proof.

Every concrete `VerifierTableauProblem` has positive formula width because its
layout allocates at least one symbol variable. Consequently its canonical
unary width header starts with `T`. Lean proves both direct coordinates:

```lean
problem.formulaBitSlotDirect 0 = some (some true)
problem.formulaBitSlotDirect 1 = some (some true)
```

and binds the emitted token to the actual canonical encoding:

```lean
CNFToken.t.bits = problem.encodedFormula.take 2
```

The theorem quantifies both verifier input modes through the general concrete
problem type.

## Fail-closed behavior and audit

Unexpected `zeroZero` in the tally scan phase and unexpected `zeroBlank` in
the token-output scan phase have no rule and are nonhalting. They remain
timeout for every fuel value instead of being reclassified as rejection.
Removing exactly the final successful transition from the first-header trace
also yields timeout.

The module exposes 68 declarations. The compiled axiom transcript records 42
with empty closure, 13 using only `propext`, and 13 using only `propext` plus
`Quot.sound`. No declaration reaches a project axiom, `Classical.choice`, or
`sorryAx`. Regression checks cover all four tokens, empty and nonempty prior
output, empty/one/odd/even/all-zero/all-one/mixed source words, arbitrary
exterior cells, exact work costs, compiled execution, both malformed phases,
one-step-short fuel, and input-only and paired formula problems. The hostile
audit mutates the alphabet, state codes, symbols, table, start request,
polynomial, endpoint, formula-bit link, malformed symbols, fuel, assumptions,
and theorem scope and requires each mutation to fail closed.

Run:

```bash
lake build PNP
lake env lean -DwarningAsError=true \
  lean-audit/PNPConcreteCookLevinBuilderTokenAppenderAxiomAudit.lean
lake env lean -DwarningAsError=true \
  lean-regression/PNPConcreteCookLevinBuilderTokenAppender.lean
node --test \
  audits/lean-concrete-cook-levin-builder-token-appender0.test.mjs
```

## Exact nonclaim

This milestone does not concatenate the input-prefix and token-appender rule
tables, compute the remaining width header, interpret a dynamic formula cursor
coordinate, emit a complete formula, or establish a construction-time
`RawRefinement`. It supplies no concrete `PolynomialReduction`, CNFSAT
NP-hardness or NP-completeness, CNFSAT-in-P theorem, or P-equals-NP theorem.
`PNP.Main.p_eq_np` remains absent and the publication gate remains false.
