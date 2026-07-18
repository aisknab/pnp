# Concrete Cook–Levin first-clause padding run

`lean/PNP/Concrete/CookLevinBuilderFirstClausePaddingRun.lean` composes the
raw-input builder through the complete first clause, its first proved padding
step, the entire remaining first-clause padding block in that fixed-width
clause rectangle, and the first coordinate of clause two. The endpoint has evaluated
the second-clause coordinate but has not emitted its separator token.

Let `V = formulaVariableSlotBound` and
`C = formulaTokensPerClause = 2 + (V + 4) * (V + 1)`. The predecessor retains
coordinate `V + 13`, immediately after consuming the first padding
opportunity. This milestone proves the exact remaining count

```text
D = (V - 1) * (V + 6) = C - 12
```

and the endpoint coordinate

```text
(V + 13) + D = V + 1 + C.
```

The right side is the first opportunity in the second clause rectangle.

## Literal countdown table and composition

`PaddingCountdown.machine` contains the complete 16-rule unary-root
controller and nine total symbol-preserving loopback rules. Its literal table
therefore has exactly 25 rules. The controller consumes one positive root
unit. A `more` exit loops to the controller start, while the `done` exit is the
only successful halt. The exact inductive trace works for every positive
materialized root and preserves the raw input, formula output, and all exterior
workspace beyond the rewritten root.

Two structurally generated unary evaluators surround that table:

1. `remainingPaddingPolynomial` materializes `D`;
2. the 25-rule table consumes all `D` units; and
3. `secondClauseStartPolynomial` materializes `V + 1 + C`.

Three nested `WorkChain` compositions add one total nine-symbol bridge at each
boundary. The complete machine's symbolic rule count is

```text
1244
+ width-evaluator ruleCount
+ body-start-coordinate evaluator ruleCount
+ first-literal-coordinate evaluator ruleCount
+ first-clause-coordinate evaluator ruleCount
+ remaining-padding evaluator ruleCount
+ second-clause-target evaluator ruleCount.
```

The constant is `1192 + 3*9 + 25`: the prior cursor-step table, three new
launch tables, and the countdown table. Only the final target evaluator's
accept and reject images are global halts. `rules_pairwise_query_distinct`
proves deterministic first-match dispatch across every renamed table and
bridge.

## Exact machine and schedule traces

`prefix_workRunExact` preserves the complete predecessor trace in the first
state image, and `launch_workStep` exposes the outer bridge. The count
evaluator, countdown, and target evaluator each have separate exact-run
theorems. `workRunExact` composes them into one all-input trace from the
ordinary raw-input work tape to the global accepting endpoint.

The schedule proof is independent of that operational trace. It unfolds the
first shape constraint far enough to prove that:

- the complete first clause occupies the first eleven positions of its
  rectangle;
- every coordinate from `V + 13` through `V + C` is valid padding;
- the coordinate `V + 1 + C` is populated by `Sep`.

Thus `paddingSlot_direct_eq_padding` proves every looped-over lookup is
`some none`, while `secondClauseStart_direct_eq_sep` proves the endpoint lookup
is `some (some Sep)`. The recursive `specificationRun` accumulates populated
tokens; `specification_padding_run` proves that all `D` steps emit the empty
list and stop at exactly the materialized target. `specification_target_step`
observes the next separator without claiming that this milestone emits it.

The formula output consequently remains the canonical prefix through the
first clause. `finalTape_represents` preserves the raw input,
`finalTokenBits_eq_encodedFormula_firstClause` preserves the exact encoded
prefix, and `finalOutside_contains_finalTokenSlot` audits the final unary root
at the second-clause coordinate.

## External compiled bound

Let `R` be the evaluated root-prefix polynomial for the remaining-padding
evaluator. The countdown satisfies

```text
countdownWorkSteps <= D * (2*R + 8) + D*D.
```

The external raw-transition polynomial evaluates to

```text
BuilderDynamicTokenCursorStep.rawTimeBound(n)
+ 18
+ 6 * Unary.workSteps(remainingPaddingPolynomial, n)
+ 6 * (D * (2*R + 8) + D*D)
+ 6 * Unary.workSteps(secondClauseStartPolynomial, n).
```

The constant 18 is exactly six compiled transitions for each of the three new
bridges. `rawTimeBound_le` proves that this polynomial bounds six times the
complete exact work trace. The compiled interfaces then establish exact
execution, polynomial-fuel execution, blank-equivalent ordinary-start
transport, acceptance, and non-timeout.

## Fail-closed boundaries and audits

The module proves timeout at the predecessor endpoint before its launch and
at exactly one work transition less than the successful trace. It also exposes
two malformed countdown configurations: a non-scratch symbol during the scan
and a separator where root consumption requires a unary unit. Both are stuck
and remain local timeout for every fuel budget.

The regression covers empty input, one-bit zero and one, odd and even lengths,
all-zero and all-one words, both verifier input modes, exact counts and
coordinates, schedule padding, the second-clause separator, all component
launches and traces, final tape/output geometry, compiled acceptance, and the
external polynomial evaluation.

```sh
lake env lean -DwarningAsError=true \
  lean-audit/PNPConcreteCookLevinBuilderFirstClausePaddingRunAxiomAudit.lean
lake env lean -DwarningAsError=true \
  lean-regression/PNPConcreteCookLevinBuilderFirstClausePaddingRun.lean
node --test \
  audits/lean-concrete-cook-levin-builder-first-clause-padding-run0.test.mjs
```

The audit covers all 83 public declarations in the new module plus the one
public equality-based controller interface added to its predecessor: 37 have
empty closure, 11 use only `propext`, and 36 use only `propext` and
`Quot.sound`. No declaration reaches a project axiom, `Classical.choice`, a
caller-supplied certificate, SAT/minimization code, or host-side composition.

## Generated publication artifacts

The mechanically regenerated publication remains fail-closed and records 32
reviewed milestones. Its reproducible outputs are:

- compiled inventory SHA-256:
  `87d085a8712794527850a495741cf3cce9cb6b38151457c0873899043b9e4c8f`;
- Lean source-closure SHA-256:
  `d7acbdace52e522810a2afb22915c9226f16363ebaec721646fda7ab4d3a3c06`;
- stable publication-map SHA-256:
  `47c2d99df4c8da006f9327c4934c3b3b18bec1df58ad51ec7b6e9414218f86a2`;
- formal-status SHA-256:
  `c4f8caec0bee56d04616fe76fc686c7065083ec46407fa8b8cfef60eed91dc4b`;
- canonical TeX SHA-256:
  `649ae65829ffa9663ee70cc009c0f0fc45b550376c1d63c45d8aeb5bfd83925e`;
- canonical PDF: 26 A4 pages, 311,223 bytes, SHA-256
  `2e59c5111601eab9097e8fa23aa09ac4a8cc9ba3785d3fd568f6cf578ffc9965`.

## Remaining boundary

This is an input-dependent run across one specifically proved padding block,
not a general dynamic formula cursor or arbitrary raw slot decoder. It does
not emit the second-clause separator, traverse later clause rectangles, branch
to all token appenders, build the remaining formula, construct a complete raw
formula builder, provide builder `RawRefinement` or a `PolynomialReduction`,
prove CNF-SAT NP-complete or in P, or establish `PNP.Main.p_eq_np`. The four
project assumptions, six blockers, unset activation fingerprints, and false
publication gate remain unchanged.
