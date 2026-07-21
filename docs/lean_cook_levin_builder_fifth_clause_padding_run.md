# Concrete Cook–Levin fifth-clause padding run

`lean/PNP/Concrete/CookLevinBuilderFifthClausePaddingRun.lean` composes the
raw-input builder through the complete fourth clause, its remaining padding,
and the entire intentionally empty fifth-clause rectangle. The endpoint is the
first opportunity in the sixth clause rectangle. That opportunity is also
intentionally empty, and this milestone emits no token.

Let `V = formulaVariableSlotBound`,
`C = formulaTokensPerClause = 2 + (V + 4) * (V + 1)`, and let
`S5 = V + 1 + 4*C` be the fifth-clause start coordinate retained by the
predecessor. This milestone proves the exact traversal count

```text
D = C
```

and endpoint

```text
S5 + D = V + 1 + 5*C.
```

The right side is the first opportunity in the sixth fixed-width clause slot.

## Literal composition

The module reuses the already-audited 25-rule
`BuilderFirstClausePaddingRun.PaddingCountdown.machine`. Two structurally
generated unary evaluators surround it:

1. `paddingPolynomial = formulaClauseTokenPolynomial` materializes `D`;
2. the countdown consumes every unit in that root; and
3. `sixthClauseSlotStartPolynomial` materializes `V + 1 + 5*C`.

Three nested `WorkChain` compositions add one total nine-symbol bridge at each
boundary. The complete symbolic rule count is

```text
4380
+ twelve inherited unary-evaluator ruleCount terms
+ fifth-rectangle evaluator ruleCount
+ sixth-clause-target evaluator ruleCount.
```

The constant is the predecessor's `4328`, three bridges, and the reused
25-rule countdown table. Only the target evaluator's accept and reject state
images are global halts. `rules_pairwise_query_distinct` proves collision-free
first-match dispatch across every renamed table and bridge.

## Exact trace and schedule semantics

`prefix_workRunExact` transports the complete fourth-clause trace and
`launch_workStep` exposes the outer bridge. The count evaluator, countdown,
and target evaluator have separate exact-run theorems. `workRunExact`
composes them into one exact execution for every raw bitstring.

The independent schedule proof unfolds the first exactly-one shape constraint
through its four populated clauses and the next two empty clause slots. It proves
that:

- every opportunity in the fifth fixed-width rectangle is padding;
- `V + 1 + 5*C` is the first token opportunity in an intentionally empty
  sixth clause rectangle.

Thus `paddingSlot_direct_eq_padding` returns `some none` for every traversed
coordinate and `sixthClauseSlotStart_direct_eq_padding` returns `some none` at
the endpoint. `specification_padding_run` emits the empty list for all `D`
steps, while `specification_target_step` observes another padding opportunity.

The formula output remains exactly the complete fourth-clause prefix:

```text
T^FormulaWidth F
Sep T F T T F T T T F Finish
Sep F F F T F Finish
Sep F F F T T F Finish
Sep F T F F T T F Finish.
```

`finalTokenBits_eq_encodedFormula_fourthClause` identifies it with
`encodedFormula.take (2 * (FormulaWidth + 36))`, and
`finalTape_represents` preserves the original raw input.

## External compiled bound

Let `R` be the evaluated root-prefix polynomial for the full-rectangle-padding
evaluator. The countdown satisfies

```text
countdownWorkSteps <= D * (2*R + 8) + D*D.
```

The external raw-transition polynomial evaluates to

```text
BuilderFourthClausePaddingRun.rawTimeBound(n)
+ 18
+ 6 * Unary.workSteps(paddingPolynomial, n)
+ 6 * (D * (2*R + 8) + D*D)
+ 6 * Unary.workSteps(sixthClauseSlotStartPolynomial, n).
```

The constant `18` is six compiled transitions for each of the three bridges.
The compiled interfaces establish exact execution, polynomial-fuel execution,
ordinary-start blank equivalence, acceptance, and non-timeout.

## Fail-closed boundaries and audit

The predecessor endpoint remains timeout before the outer launch, and one work
step less than the exact successful trace remains timeout. A malformed scratch
marker during the countdown scan and a separator where root consumption
requires a unit are stuck and remain timeout for every local fuel budget.

The regression covers empty input, one-bit zero and one, odd and even lengths,
all-zero and all-one inputs, input-only and paired verifier modes, exact counts
and coordinates, all component launches and traces, exact fourth-clause
output, the entire empty fifth-clause rectangle, the empty sixth-clause endpoint,
compiled acceptance, and the external polynomial evaluation.

```sh
lake env lean -DwarningAsError=true \
  lean-audit/PNPConcreteCookLevinBuilderFifthClausePaddingRunAxiomAudit.lean
lake env lean -DwarningAsError=true \
  lean-regression/PNPConcreteCookLevinBuilderFifthClausePaddingRun.lean
node --test \
  audits/lean-concrete-cook-levin-builder-fifth-clause-padding-run0.test.mjs
```

The combined audit covers all 65 public declarations in the module and three
reused countdown interfaces. Exactly 28 closures are empty, 9 use only
`propext`, and 31 use only `propext` and `Quot.sound`. It rejects project axioms,
`Classical.choice`, `sorry`, `admit`, native or SAT shortcuts, host-side
schedule lookup, and caller-supplied execution certificates.

## Generated publication artifacts

The compiled environment records inventory coordinate
`PNP-LEAN-THEOREM-INVENTORY-2026-07-22-68`, 10,049 declarations, 5,476
theorems, 3,272 assumption-free theorems, 88 source-closure modules, and 1,408
reviewed milestone candidates. Its canonical byte SHA-256 is
`db681f0f80c03980c03daec19163be30662789e0c665cc283994d1ea3dc10ccd`;
the Lean source-closure SHA-256 is
`45c8bca48241157a31c64ece179a1c99b2515476b80e093010976df3dfdba6ae`.

Publication map coordinate `PNP-FORMAL-PUBLICATION-MAP-2026-07-22-68` has
48 milestones, 45 earned milestones, and 1,408 exact kernel-type fingerprints. Its exact file
SHA-256 is
`0ffa3a87b6b9ab0db3b17b7db7b7b9bef43e57a5b0748a701516dd359f4d379c`,
and its canonical reviewed-object fingerprint is
`6fffe4eff8e91621ce47733dd277b44dd4534f3b3724438204755563b9961934`.

Status coordinate `PNP-FORMAL-RECONSTRUCTION-STATUS-2026-07-22-68` has
SHA-256 `b1b27d1d14eb4ef261cbf534a17526cf24dc68e3dc4ffd2d4a2ba06b566e6122`.
The generated report coordinate is
`PNP-CANONICAL-FORMAL-RECONSTRUCTION-REPORT-2026-07-22-68`; its 100,199-byte
TeX SHA-256 is `e913ca4b58645a90d6a49b76dae2f1f3a4452663af18b8c5909f50455b1d80c6`
and its 44-page, 356,778-byte PDF SHA-256 is
`4f78aea8188173ed03c849248c451d5fe52c6e9bbe000c286b45eafee9110fec`.
All activation fingerprints remain unset and the publication gate remains
false.

## Remaining boundary

This is one input-dependent traversal of one specifically proved padding
rectangle, not a general dynamic formula cursor or arbitrary raw slot decoder.
It does not traverse the empty sixth clause rectangle, reach the next
constraint, emit another token, emit the remaining formula body, construct a
complete raw formula builder, provide builder `RawRefinement` or a
`PolynomialReduction`, prove CNF-SAT NP-complete or in P, or establish
`PNP.Main.p_eq_np`. The four project assumptions, six blockers, unset
activation fingerprints, and false publication gate remain unchanged.
