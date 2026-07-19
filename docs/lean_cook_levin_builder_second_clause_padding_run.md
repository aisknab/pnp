# Concrete Cook–Levin second-clause padding run

`lean/PNP/Concrete/CookLevinBuilderSecondClausePaddingRun.lean` composes the
raw-input builder through the complete second clause, the entire remaining
second-clause padding block, and the first coordinate of clause three. The
endpoint has evaluated the third-clause coordinate but has not emitted its
separator token.

Let `V = formulaVariableSlotBound`,
`C = formulaTokensPerClause = 2 + (V + 4) * (V + 1)`, and let `S` be the
second-clause start coordinate. The predecessor retains `S + 7`, the first
padding opportunity after the seven populated tokens in clause two. This
milestone proves the exact count

```text
D = (V - 1) * (V + 6) + 5 = C - 7
```

and endpoint

```text
(S + 7) + D = V + 1 + 2*C.
```

The right side is the first opportunity in the third clause rectangle.

## Literal composition

The module reuses the already-audited 25-rule
`BuilderFirstClausePaddingRun.PaddingCountdown.machine`. Two structurally
generated unary evaluators surround it:

1. `remainingPaddingPolynomial` materializes `D`;
2. the countdown consumes every unit in that root; and
3. `thirdClauseStartPolynomial` materializes `V + 1 + 2*C`.

Three nested `WorkChain` compositions add one total nine-symbol bridge at
each boundary. The complete symbolic rule count is

```text
2150
+ six inherited unary-evaluator ruleCount terms
+ remaining-padding evaluator ruleCount
+ third-clause-target evaluator ruleCount.
```

The constant is the predecessor's `2098`, three bridges, and the reused
25-rule countdown table. Only the target evaluator's accept and reject state
images are global halts. `rules_pairwise_query_distinct` proves collision-free
first-match dispatch across every renamed table and bridge.

## Exact trace and schedule semantics

`prefix_workRunExact` transports the complete second-clause trace and
`launch_workStep` exposes the outer bridge. The count evaluator, countdown,
and target evaluator have separate exact-run theorems. `workRunExact`
composes them into one exact execution for every raw bitstring.

The independent schedule proof unfolds the first exactly-one shape constraint
through its first three clauses. It proves that:

- clause two occupies seven populated token slots;
- every coordinate from `S + 7` through the end of that rectangle is padding;
- `V + 1 + 2*C` is populated by the `Sep` beginning clause three.

Thus `paddingSlot_direct_eq_padding` returns `some none` for every traversed
coordinate and `thirdClauseStart_direct_eq_sep` returns
`some (some Sep)` at the endpoint. `specification_padding_run` emits the empty
list for all `D` steps, while `specification_target_step` observes the next
separator without claiming that this machine emits it.

The formula output remains exactly

```text
T^FormulaWidth F Sep T F T T F T T T F Finish Sep F F F T F Finish.
```

`finalTokenBits_eq_encodedFormula_secondClause` identifies it with
`encodedFormula.take (2 * (FormulaWidth + 19))`, and
`finalTape_represents` preserves the original raw input.

## External compiled bound

Let `R` be the evaluated root-prefix polynomial for the remaining-padding
evaluator. The countdown satisfies

```text
countdownWorkSteps <= D * (2*R + 8) + D*D.
```

The external raw-transition polynomial evaluates to

```text
BuilderSecondClausePrefix.rawTimeBound(n)
+ 18
+ 6 * Unary.workSteps(remainingPaddingPolynomial, n)
+ 6 * (D * (2*R + 8) + D*D)
+ 6 * Unary.workSteps(thirdClauseStartPolynomial, n).
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
coordinates, all component launches and traces, second-clause output,
clause-two padding, the clause-three separator, compiled acceptance, and the
external polynomial evaluation.

```sh
lake env lean -DwarningAsError=true \
  lean-audit/PNPConcreteCookLevinBuilderSecondClausePaddingRunAxiomAudit.lean
lake env lean -DwarningAsError=true \
  lean-regression/PNPConcreteCookLevinBuilderSecondClausePaddingRun.lean
node --test \
  audits/lean-concrete-cook-levin-builder-second-clause-padding-run0.test.mjs
```

The combined audit covers all 65 public declarations in the module and three
reused countdown interfaces. Exactly 26 declarations have empty closure, nine
use only `propext`, and 33 use only `propext` and `Quot.sound`. No declaration
reaches a project axiom, `Classical.choice`, `sorry`, `admit`, SAT or
minimization code, host-side composition, or a caller-supplied execution
certificate.

## Generated publication artifacts

The compiled environment records inventory coordinate
`PNP-LEAN-THEOREM-INVENTORY-2026-07-19-57`, 8,599 declarations, 4,359
theorems, 3,031 assumption-free theorems, 77 source-closure modules, and 878
reviewed milestone candidates. Its canonical byte SHA-256 is
`6c167d3b1e92f52ff8736fc349b3f1cdff105dee4636f48fc57b41b731259b30`;
the Lean source-closure SHA-256 is
`bc78667ff2331b3658d50babb93c36927449453cfb0b36acb4e2779f0b2efec9`.

Publication map coordinate `PNP-FORMAL-PUBLICATION-MAP-2026-07-19-57` has
37 milestones and 878 exact kernel-type fingerprints. Its exact file SHA-256
is `d38a05b53ea2a86569f60966b1991cb22be34ee3e53d4b972811acabe5348369`,
and its canonical reviewed-object fingerprint is
`3ebe668d91bcdfed93006dbcd826e8a6aed04a11efbf7224f73b8d3b9d413f59`.

Status coordinate `PNP-FORMAL-RECONSTRUCTION-STATUS-2026-07-19-57` has
SHA-256 `56fa058bbb6250a422db16860e77a5cf6fc8555fdd3d1a10631297c435259084`.
The generated report coordinate is
`PNP-CANONICAL-FORMAL-RECONSTRUCTION-REPORT-2026-07-19-57`; its TeX SHA-256
is `5298f903836359cf641308d70a7075658a0df78add4eca58c35ec94581bd98b9`
and its 32-page, 324,463-byte PDF SHA-256 is
`ee5dd3d286c209131fd7c0a493f26f1f3dc6168c6d5aa24ff1847a94666269dd`.
All activation fingerprints remain unset and the publication gate remains
false.

## Remaining boundary

This is one input-dependent traversal of one specifically proved padding
rectangle, not a general dynamic formula cursor or arbitrary raw slot decoder.
It reaches clause three as a retained coordinate but does not emit its
separator, emit the remaining formula body, construct a complete raw formula
builder, provide builder `RawRefinement` or a `PolynomialReduction`, prove
CNF-SAT NP-hard or NP-complete or in P, or establish `PNP.Main.p_eq_np`. The
four project assumptions, six blockers, unset activation fingerprints, and
false publication gate remain unchanged.
