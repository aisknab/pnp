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
reused countdown interfaces. It rejects project axioms,
`Classical.choice`, `sorry`, `admit`, native or SAT shortcuts, host-side
schedule lookup, and caller-supplied execution certificates.

## Generated publication artifacts

The compiled environment records inventory coordinate
`PNP-LEAN-THEOREM-INVENTORY-2026-07-21-67`, 9,906 declarations, 5,367
theorems, 3,252 assumption-free theorems, 87 source-closure modules, and 1,371
reviewed milestone candidates. Its canonical byte SHA-256 is
`6431a458dbb72513518ecb2b64fb9cd5813323130f49c281df18cd3933da4c16`;
the Lean source-closure SHA-256 is
`2a69acbcb5db358a7b85d0994847dd23a0fddc749cf9e3c73febc55e240ba581`.

Publication map coordinate `PNP-FORMAL-PUBLICATION-MAP-2026-07-21-67` has
47 milestones and 1,371 exact kernel-type fingerprints. Its exact file
SHA-256 is
`330d204ca47ddd6dbd44e6b83dbd0796559afea5c3592775c67899e3028cc0f9`,
and its canonical reviewed-object fingerprint is
`da7f64e7b5833bc4d4399dd191a943a6ceb1fd5aef8d722deaa9d2cb26fdfcbd`.

Status coordinate `PNP-FORMAL-RECONSTRUCTION-STATUS-2026-07-21-67` has
SHA-256 `f59c5a127e0e8d635d5a7283cbc1c5cd70fd9ed2401008cf2164e96b3dda01d6`.
The generated report coordinate is
`PNP-CANONICAL-FORMAL-RECONSTRUCTION-REPORT-2026-07-21-67`; its 98,064-byte
TeX SHA-256 is `6a22031e8a428a174dcfeb6b31a8a4e02ded30add67041f7dc750bd243669d3c`
and its 43-page, 352,982-byte PDF SHA-256 is
`ac4c86c2d9658ed4d8b005f388739cbcd6a9931d9b2925af8535ac191ad83d34`.
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
