# Concrete Cook–Levin first-clause-prefix machine

`lean/PNP/Concrete/CookLevinBuilderFirstClausePrefix.lean` defines one
literal finite work machine that extends the first-literal milestone through
the complete first canonical Cook–Levin clause. Starting from an ordinary raw
`BitString`, it runs the existing first-literal prefix, constructs the next
token-schedule coordinate in unary scratch, and appends the remaining fixed
tokens for positive variables one and two and the clause terminator.

Its exact output token list is

```text
T repeated FormulaWidth times, followed by
F, Sep, T, F, T, T, F, T, T, T, F, Finish
```

The three literals are positive variables zero, one, and two. Their token
pairs are exactly
`encodedFormula.take (2 * (FormulaWidth + 12))`. This milestone does not
implement a dynamic cursor, emit the remaining clauses, construct the
complete formula, supply a builder `RawRefinement`, package a
`PolynomialReduction`, decide CNF-SAT, or prove `P = NP`.

## Literal composition and rule table

The module uses one generic bridge-first sequential constructor. Its two
state maps are the already-audited `inputState` and `simulationState`; their
injectivity and disjointness are proved. Each composition contributes nine
symbol-preserving launch rules, followed by renamed copies of both complete
component tables. Only the second component's accept and reject images are
global halts.

The fixed tail is eight complete 59-rule token appenders joined by seven
nine-rule bridges:

```text
8 * 59 + 7 * 9 = 535 rules.
```

The outer machine joins the existing first-literal prefix to a fresh unary
coordinate evaluator and then to that fixed tail. Its exact symbolic rule
count is

```text
1138
+ width-evaluator ruleCount
+ body-start next-slot-evaluator ruleCount
+ first-literal next-slot-evaluator ruleCount
+ first-clause next-slot-evaluator ruleCount.
```

`rules_pairwise_query_distinct` audits each bridge, renamed component, and
cross-image pair. The predecessor module now also exposes the proved fact
that no local rule leaves its accepting state, preventing the new outer
bridge from being shadowed.

## Retained coordinate

The structurally compiled polynomial

```text
formulaVariableCountPolynomial + 12
```

evaluates to `formulaVariableSlotBound + 12`, the token opportunity
immediately after the first clause. The specification-only `nextBitCursor`
records the corresponding bit coordinate
`2 * (formulaVariableSlotBound + 12)`. The finite machine materializes the
token coordinate as a unary root register but does not execute a dynamic
schedule lookup.

## Exact clause semantics and trace

The semantic proof follows the first scheduled shape constraint to the
at-least-one symbol clause at time zero and tape position zero. The canonical
tape-symbol order is blank, zero, one, whose flattened variable indices at
that location are exactly zero, one, and two. The emitted clause is therefore

```text
Sep, positive 0, positive 1, positive 2, Finish.
```

`firstClauseTokens_eq_canonical_formula_prefix` proves that this list is an
actual prefix of `encodeCNFTokens problem.formula`.
`finalTokenBits_eq_encodedFormula_firstClause` then identifies every emitted
bit with the corresponding canonical encoded-formula bit. No caller supplies
a trace, certificate, SAT result, or minimizing witness.

The successful work trace is

```text
complete first-literal-prefix work
+ 1 outer bridge
+ exact unary first-clause-next-coordinate evaluation
+ 1 inner bridge
+ eight exact token appends with seven internal bridges.
```

The outer and inner launch theorems expose both bridge transitions.
`workRunExact` proves the complete all-input run, and `finalTape_represents`
proves that the original raw input remains represented at the endpoint.

## External compiled-time polynomial

Let `n` be the raw input length and `W = FormulaWidth`. The public
`rawTimeBound` evaluates exactly to

```text
FirstLiteralPrefix.rawTimeBound(n)
+ 1158
+ 6 * Unary.workSteps(firstClauseNextTokenSlotPolynomial, input)
+ 192*n
+ 96*W.
```

The eight appender runs, seven internal launches, and two enclosing launches
account for the new constants. `rawTimeBound_le` proves that this external
polynomial bounds six times the exact work trace. The compiled theorems prove
the same endpoint at exact and polynomial fuel, transport it from the ordinary
blank-equivalent raw start, and establish both compiled and work-level
acceptance.

## Fail-closed boundaries

The module proves timeout at the deliberately incomplete or malformed
boundaries that are new to this composition:

- the first-literal endpoint before the outer launch;
- the unary evaluator endpoint before the inner launch;
- malformed tally and output symbols in the first tail appender; and
- exactly one work transition less than the successful trace.

The determinism proof and hostile audit additionally reject a state-map
collision, bridge removal, bridge shadowing, and altered clause bits.

## Kernel, regression, and hostile audits

The audit prints all 77 public declarations in the new module plus the one
new predecessor separation theorem:

```sh
lake env lean -DwarningAsError=true \
  lean-audit/PNPConcreteCookLevinBuilderFirstClausePrefixAxiomAudit.lean
```

Every declaration closes over only the approved Lean-standard axioms
`propext` and `Quot.sound`. None reaches `Classical.choice`, a project axiom,
`sorryAx`, `admit`, a SAT/minimization call, host composition, or a
caller-supplied certificate.

The regression module covers empty input, one-bit zero and one, odd and even
lengths, all-zero and all-one inputs, input-only and paired verifiers, exact
rule and step counts, both launches, final tape and token bits, compiled
acceptance, polynomial evaluation, malformed configurations, and shortened
fuel:

```sh
lake env lean -DwarningAsError=true \
  lean-regression/PNPConcreteCookLevinBuilderFirstClausePrefix.lean
node --test \
  audits/lean-concrete-cook-levin-builder-first-clause-prefix0.test.mjs
```

## Remaining boundary

Exactly one canonical clause is emitted beyond the header. A dynamic slot
interpreter, remaining formula body, complete builder, builder refinement,
concrete reduction, CNF-SAT NP-completeness and in-P results, and
`PNP.Main.p_eq_np` all remain absent. The four disclosed project assumptions,
six reconstruction blockers, unset activation fingerprints, and false
publication gate are unchanged.
