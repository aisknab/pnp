# Concrete Cook–Levin third-clause padding run

`lean/PNP/Concrete/CookLevinBuilderThirdClausePaddingRun.lean` composes the
raw-input builder through the complete third clause, the entire remaining
third-clause padding block, and the first coordinate of clause four. The
endpoint has evaluated the fourth-clause coordinate but has not emitted its
separator token.

Let `V = formulaVariableSlotBound`,
`C = formulaTokensPerClause = 2 + (V + 4) * (V + 1)`, and let `S` be the
third-clause start coordinate. The predecessor retains `S + 8`, the first
padding opportunity after the eight populated tokens in clause three. This
milestone proves the exact count

```text
D = (V - 1) * (V + 6) + 4 = C - 8
```

and endpoint

```text
(S + 8) + D = V + 1 + 3*C.
```

The right side is the first opportunity in the fourth clause rectangle.

## Literal composition

The module reuses the already-audited 25-rule
`BuilderFirstClausePaddingRun.PaddingCountdown.machine`. Two structurally
generated unary evaluators surround it:

1. `remainingPaddingPolynomial` materializes `D`;
2. the countdown consumes every unit in that root; and
3. `fourthClauseStartPolynomial` materializes `V + 1 + 3*C`.

Three nested `WorkChain` compositions add one total nine-symbol bridge at
each boundary. The complete symbolic rule count is

```text
3178
+ eight inherited unary-evaluator ruleCount terms
+ remaining-padding evaluator ruleCount
+ fourth-clause-target evaluator ruleCount.
```

The constant is the predecessor's `3126`, three bridges, and the reused
25-rule countdown table. Only the target evaluator's accept and reject state
images are global halts. `rules_pairwise_query_distinct` proves collision-free
first-match dispatch across every renamed table and bridge.

## Exact trace and schedule semantics

`prefix_workRunExact` transports the complete third-clause trace and
`launch_workStep` exposes the outer bridge. The count evaluator, countdown,
and target evaluator have separate exact-run theorems. `workRunExact`
composes them into one exact execution for every raw bitstring.

The independent schedule proof unfolds the first exactly-one shape constraint
through all four clauses. It proves that:

- clause three occupies eight populated token slots;
- every coordinate from `S + 8` through the end of that rectangle is padding;
- `V + 1 + 3*C` is populated by the `Sep` beginning clause four.

Thus `paddingSlot_direct_eq_padding` returns `some none` for every traversed
coordinate and `fourthClauseStart_direct_eq_sep` returns
`some (some Sep)` at the endpoint. `specification_padding_run` emits the empty
list for all `D` steps, while `specification_target_step` observes the next
separator without claiming that this machine emits it.

The formula output remains exactly

```text
T^FormulaWidth F Sep T F T T F T T T F Finish
Sep F F F T F Finish Sep F F F T T F Finish.
```

`finalTokenBits_eq_encodedFormula_thirdClause` identifies it with
`encodedFormula.take (2 * (FormulaWidth + 27))`, and
`finalTape_represents` preserves the original raw input.

## External compiled bound

Let `R` be the evaluated root-prefix polynomial for the remaining-padding
evaluator. The countdown satisfies

```text
countdownWorkSteps <= D * (2*R + 8) + D*D.
```

The external raw-transition polynomial evaluates to

```text
BuilderThirdClausePrefix.rawTimeBound(n)
+ 18
+ 6 * Unary.workSteps(remainingPaddingPolynomial, n)
+ 6 * (D * (2*R + 8) + D*D)
+ 6 * Unary.workSteps(fourthClauseStartPolynomial, n).
```

The constant `18` is six compiled transitions for each of the three bridges.
The compiled interfaces establish exact execution, polynomial-fuel execution,
ordinary-start blank equivalence, acceptance, and non-timeout.

## Fail-closed boundaries and audit

The predecessor endpoint remains timeout before the outer launch, and one
work step less than the exact successful trace remains timeout. A malformed
scratch marker during the countdown scan and a separator where root
consumption requires a unit are stuck and remain timeout for every local fuel
budget.

The regression covers empty input, one-bit zero and one, odd and even lengths,
all-zero and all-one inputs, both verifier input modes, exact counts and
coordinates, all component launches and traces, third-clause output,
clause-three padding, the clause-four separator, compiled acceptance, and the
external polynomial evaluation.

```sh
lake env lean -DwarningAsError=true \
  lean-audit/PNPConcreteCookLevinBuilderThirdClausePaddingRunAxiomAudit.lean
lake env lean -DwarningAsError=true \
  lean-regression/PNPConcreteCookLevinBuilderThirdClausePaddingRun.lean
node --test \
  audits/lean-concrete-cook-levin-builder-third-clause-padding-run0.test.mjs
```

The combined audit covers all 65 public declarations in the module and three
reused countdown interfaces. Exactly 26 declarations have empty closure, nine
use only `propext`, and 33 use only `propext` and `Quot.sound`. No declaration
reaches a project axiom, `Classical.choice`, `sorry`, `admit`, SAT or
minimization code, host-side composition, or a caller-supplied execution
certificate.

## Generated publication artifacts

The compiled environment records inventory coordinate
`PNP-LEAN-THEOREM-INVENTORY-2026-07-20-62`, 9,251 declarations, 4,864
theorems, 3,140 assumption-free theorems, 82 source-closure modules, and 1,126
reviewed milestone candidates. Its canonical byte SHA-256 is
`be49e777c8d5fe6ca74fe4bcb808e67157091fc9c2f15502da7649e64e7287c4`;
the Lean source-closure SHA-256 is
`522c47713a55db0605db09c3340b39de686139ff45f5259d087a068a8bfe7db6`.

Publication map coordinate `PNP-FORMAL-PUBLICATION-MAP-2026-07-20-62` has
42 milestones and 1,126 exact kernel-type fingerprints. Its exact file SHA-256
is `826a580fcebc4b5f115023c57e870b866a63927ebf04e6475476c73019388f6d`,
and its canonical reviewed-object fingerprint is
`f085d50a19201eb132474479bc6b660a4a9db6dd10297bd74da12c1eabfe0af4`.

Status coordinate `PNP-FORMAL-RECONSTRUCTION-STATUS-2026-07-20-62` has
SHA-256 `30d1c9c9dca12e13da089f312b9df023001ecdf3687850da64a6ef797c4a1057`.
The generated report coordinate is
`PNP-CANONICAL-FORMAL-RECONSTRUCTION-REPORT-2026-07-20-62`; its TeX SHA-256
is `333f2cd48175ad2e50850f2bb61b144b826b2c2b4f262e664c9dcd2ed9ae29ee`
and its 37-page, 338,355-byte PDF SHA-256 is
`92a782f234597457a50fbc9c9f319b1a202d743f4320c9d9e10a508fac50895a`.
All activation fingerprints remain unset and the publication gate remains
false.

## Remaining boundary

This is one input-dependent traversal of one specifically proved padding
rectangle, not a general dynamic formula cursor or arbitrary raw slot decoder.
It reaches clause four as a retained coordinate but does not emit its
separator, emit the remaining formula body, construct a complete raw formula
builder, provide builder `RawRefinement` or a `PolynomialReduction`, prove
CNF-SAT NP-hard or NP-complete or in P, or establish `PNP.Main.p_eq_np`. The
four project assumptions, six blockers, unset activation fingerprints, and
false publication gate remain unchanged.
