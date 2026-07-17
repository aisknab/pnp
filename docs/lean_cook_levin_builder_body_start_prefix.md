# Concrete Cook–Levin body-start-prefix machine

`lean/PNP/Concrete/CookLevinBuilderBodyStartPrefix.lean` defines one literal
finite work machine for the next bounded builder milestone. Starting from an
ordinary raw `BitString`, it runs the complete unary-width-header machine,
constructs the next token-schedule coordinate in unary scratch, and appends
the first canonical formula-body separator.

Its exact output token list is

```text
T repeated FormulaWidth times, followed by F, followed by Sep
```

Those token pairs equal
`encodedFormula.take (2 * (FormulaWidth + 2))`. This milestone does not
implement a dynamic cursor, inspect an arbitrary schedule coordinate, emit a
literal or complete clause, construct the complete formula, supply a builder
`RawRefinement`, package a `PolynomialReduction`, decide CNF-SAT, or prove
`P = NP`.

## Literal three-component composition

The machine places three complete components in the existing collision-free
state namespace:

| Component | State image |
| --- | --- |
| Complete width header | `inputState state` |
| Unary next-token-coordinate evaluator | `simulationState state` |
| Separator token appender | `handoffState state` |

The maps are proved injective and pairwise disjoint. Two nine-symbol-total
bridge tables connect the header accept endpoint to the evaluator start and
the evaluator accept endpoint to the separator appender. The bridges precede
the renamed component tables so endpoint dispatch is explicit. Only the
appender's accept and reject images are global halts.

For a verifier problem, the exact literal rule count is

```text
18 bridge rules
+ (363 + width-evaluator ruleCount) complete-header rules
+ next-token-evaluator ruleCount
+ 59 appender rules
= 440 + width-evaluator ruleCount + next-token-evaluator ruleCount.
```

`rules_pairwise_query_distinct` audits every cross-table pair as well as each
component. The proof separately establishes that neither bridge source is
already a source in the renamed component table, so first-match lookup cannot
silently shadow a transition.

## Retained cursor coordinate

The structurally compiled polynomial

```text
formulaVariableCountPolynomial + 2
```

evaluates to `formulaVariableSlotBound + 2`. This is the token opportunity
immediately after the separator just emitted: the padded width header occupies
`formulaVariableSlotBound + 1` opportunities, and the separator occupies the
next opportunity. `finalOutside_contains_nextTokenSlot` proves that the final
exterior-left workspace contains an exact unary root register for this token
coordinate.

The specification-only `nextBitCursor` records the corresponding raw-bit
coordinate `2 * (formulaVariableSlotBound + 2)`. The finite machine does not
execute that cursor or perform a dynamic lookup; retaining and relating the
coordinate is the boundary of this milestone.

## Exact canonical token and trace

`firstBodyTokenSlotDirect_eq_separator` proves that the first physical token
opportunity after the padded header is populated by `Sep`. Its constructive
proof follows the scheduled shape/initial constraints and does not use
`Classical.choice`. `finalTokenBits_eq_encodedFormula_bodyStart` then connects
the emitted token pairs to the exact canonical encoded-formula prefix.

The successful work trace is

```text
complete-header work
+ 1 bridge
+ exact unary next-token evaluation
+ 1 bridge
+ exact separator append.
```

The component transport theorems, both launch theorems, and `workRunExact`
state this composition without accepting a caller-supplied trace or
certificate. `finalTape_represents` proves that the source input remains
represented at the endpoint.

## External compiled-time polynomial

Let `n` be the raw input length and `W = FormulaWidth`. The public
`rawTimeBound` is an external `NatPolynomial` whose evaluation is exactly

```text
completeHeader.rawTimeBound(n)
+ 72
+ 6 * Unary.workSteps(nextTokenSlotPolynomial, input)
+ 24*n
+ 12*W.
```

The last two terms bound the appender scan over the preserved input and the
existing `W + 1` header tokens. `rawTimeBound_le` proves that this polynomial
bounds six times the exact work trace. The compiled theorems establish the
same endpoint at exact and polynomial fuel, transport it to the ordinary
blank-equivalent start configuration, and prove both raw and work-level
acceptance.

## Fail-closed boundaries

The module proves timeout at each deliberately incomplete boundary:

- the header endpoint before its launch;
- a renamed internal header reject endpoint;
- the unary cursor endpoint before its launch;
- the unary evaluator's isolated dead state;
- malformed appender tally and output symbols; and
- exactly one work transition less than the successful trace.

Thus bridge removal, malformed workspace data, or shortened fuel cannot be
reclassified as global acceptance.

## Kernel, regression, and hostile audits

The complete 60-declaration public surface is printed by:

```sh
lake env lean -DwarningAsError=true \
  lean-audit/PNPConcreteCookLevinBuilderBodyStartPrefixAxiomAudit.lean
```

Every declaration closes over only the approved Lean-standard axioms
`propext` and `Quot.sound`; none reaches `Classical.choice`, a project axiom,
`sorryAx`, or an unaudited assumption.

The regression module covers empty, one-bit zero/one, odd, even, all-zero,
all-one, input-only, and paired-verifier inputs; concrete rule and runtime
evaluations; both exact launches; retained token/bit coordinates; final tape
and canonical token bits; compiled acceptance; and every timeout boundary:

```sh
lake env lean -DwarningAsError=true \
  lean-regression/PNPConcreteCookLevinBuilderBodyStartPrefix.lean
node --test \
  audits/lean-concrete-cook-levin-builder-body-start-prefix0.test.mjs
```

The hostile source audit rejects assumptions and shortcuts, a state-image
collision, either bridge's removal or shadowing, host composition in the
literal table, an altered retained coordinate, and altered separator bits.

## Remaining boundary

Exactly one fixed answer-independent formula-body token is emitted beyond the
complete header. A dynamic slot interpreter, body controller, literal and
clause emission, complete builder, builder refinement, concrete reduction,
CNF-SAT NP-completeness and in-P results, and `PNP.Main.p_eq_np` all remain
absent. The four disclosed project assumptions, six reconstruction blockers,
unset activation fingerprints, and false publication gate are unchanged.
