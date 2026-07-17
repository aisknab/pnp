# Concrete Cook–Levin first-literal-prefix machine

`lean/PNP/Concrete/CookLevinBuilderFirstLiteralPrefix.lean` defines one
literal finite work machine for the next bounded builder milestone. Starting
from an ordinary raw `BitString`, it runs the complete body-start prefix,
constructs the next token-schedule coordinate in unary scratch, and appends
the first canonical literal as fixed `T` and `F` tokens.

Its exact output token list is

```text
T repeated FormulaWidth times, followed by F, Sep, T, F
```

The last two tokens encode the positive sign and unary-zero terminator of
positive variable zero. Their token pairs extend the proved canonical prefix
to
`encodedFormula.take (2 * (FormulaWidth + 4))`. This milestone does not
implement a dynamic cursor, emit the rest of the first clause, construct the
complete formula, supply a builder `RawRefinement`, package a
`PolynomialReduction`, decide CNF-SAT, or prove `P = NP`.

## Literal four-component composition

The machine places four complete components in one collision-free state
namespace:

| Component | State image |
| --- | --- |
| Complete body-start prefix | `prefixState state` |
| Unary next-token-coordinate evaluator | `evaluatorState state` |
| Fixed `T` token appender | `tAppenderState state` |
| Fixed `F` token appender | `fAppenderState state` |

The maps are proved injective and pairwise disjoint. Three nine-symbol-total
bridge tables connect the body-start accept endpoint to the evaluator, the
evaluator to the `T` appender, and the `T` appender to the `F` appender. The
bridges precede the renamed component tables so endpoint dispatch is
explicit. Only the final appender's accept and reject images are global halts.

For a verifier problem, the exact literal rule count is

```text
585
+ width-evaluator ruleCount
+ body-start next-slot-evaluator ruleCount
+ first-literal next-slot-evaluator ruleCount.
```

The constant contains all 27 bridge rules, fixed controllers, and four
appender copies inherited or added by the nested composition.
`rules_pairwise_query_distinct` audits every bridge, component, and cross-table
pair. The proof also establishes that bridge sources are not component-rule
sources, so first-match lookup cannot silently shadow a transition.

## Retained cursor coordinate

The structurally compiled polynomial

```text
formulaVariableCountPolynomial + 4
```

evaluates to `formulaVariableSlotBound + 4`. This is the token opportunity
immediately after the first literal: the padded width header occupies
`formulaVariableSlotBound + 1` opportunities, followed by the separator,
positive sign, and zero-variable terminator.
`finalOutside_contains_nextTokenSlot` proves that the final exterior-left
workspace contains an exact unary root register for this coordinate.

The specification-only `nextBitCursor` records the corresponding raw-bit
coordinate `2 * (formulaVariableSlotBound + 4)`. The finite machine does not
execute that cursor or perform a dynamic lookup; retaining and relating the
coordinate is the boundary of this milestone.

## Exact canonical literal and trace

The canonical proof follows the first scheduled constraint to the exact-one
symbol clause at time zero and tape position zero. Its first at-least-one
literal is the positive blank-symbol variable with flattened variable index
zero. Consequently:

- `firstLiteralSignSlotDirect_eq_t` pins the direct sign slot to `T`;
- `firstLiteralZeroTerminatorSlotDirect_eq_f` pins the following unary-zero
  terminator to `F`; and
- `finalTokenBits_eq_encodedFormula_firstLiteral` identifies every emitted
  bit with the canonical encoded-formula prefix.

These proofs are constructive and do not use `Classical.choice`.

The successful work trace is

```text
complete body-start-prefix work
+ 1 bridge
+ exact unary next-token evaluation
+ 1 bridge
+ exact T append
+ 1 bridge
+ exact F append.
```

The four component transport theorems, three launch theorems, and
`workRunExact` state this composition without accepting a caller-supplied
trace or certificate. `finalTape_represents` proves that the source input
remains represented at the endpoint.

## External compiled-time polynomial

Let `n` be the raw input length and `W = FormulaWidth`. The public
`rawTimeBound` is an external `NatPolynomial` whose evaluation is exactly

```text
BodyStartPrefix.rawTimeBound(n)
+ 174
+ 6 * Unary.workSteps(firstLiteralNextTokenSlotPolynomial, input)
+ 48*n
+ 24*W.
```

The final two terms bound both token appenders over the preserved input and
existing token prefix. `rawTimeBound_le` proves that this polynomial bounds
six times the exact work trace. The compiled theorems establish the same
endpoint at exact and polynomial fuel, transport it to the ordinary
blank-equivalent start configuration, and prove both raw and work-level
acceptance.

## Fail-closed boundaries

The module proves timeout at each deliberately incomplete or malformed
boundary:

- the body-start endpoint before its launch;
- a renamed internal body-start reject endpoint;
- the unary evaluator endpoint before its launch;
- the evaluator's isolated dead state;
- the `T` appender endpoint before the `F` launch;
- malformed tally or output symbols in either appender copy; and
- exactly one work transition less than the successful trace.

Thus a state-map collision, bridge removal or shadowing, malformed workspace,
altered token, or shortened fuel cannot be reclassified as global acceptance.

## Kernel, regression, and hostile audits

The complete 74-declaration public surface is printed by:

```sh
lake env lean -DwarningAsError=true \
  lean-audit/PNPConcreteCookLevinBuilderFirstLiteralPrefixAxiomAudit.lean
```

Every declaration closes over only the approved Lean-standard axioms
`propext` and `Quot.sound`; none reaches `Classical.choice`, a project axiom,
`sorryAx`, or an unaudited assumption.

The regression module covers empty, one-bit zero/one, odd, even, all-zero,
all-one, input-only, and paired-verifier inputs; concrete rules, retained
coordinates, exact traces, final tape and token bits, compiled acceptance,
polynomial evaluation, all three launches, and every timeout boundary:

```sh
lake env lean -DwarningAsError=true \
  lean-regression/PNPConcreteCookLevinBuilderFirstLiteralPrefix.lean
node --test \
  audits/lean-concrete-cook-levin-builder-first-literal-prefix0.test.mjs
```

The hostile source audit rejects assumptions and shortcuts, a state-image
collision, bridge removal or shadowing, host composition in the literal
table, an altered retained coordinate, and altered first-literal bits.

## Remaining boundary

Exactly the first canonical literal is emitted beyond the body-opening
separator. A dynamic slot interpreter, body controller, remaining literals
and clauses, complete builder, builder refinement, concrete reduction,
CNF-SAT NP-completeness and in-P results, and `PNP.Main.p_eq_np` all remain
absent. The four disclosed project assumptions, six reconstruction blockers,
unset activation fingerprints, and false publication gate are unchanged.
