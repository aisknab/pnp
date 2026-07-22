# Concrete Cook–Levin first-constraint padding run

`lean/PNP/Concrete/CookLevinBuilderFirstConstraintPaddingRun.lean` extends the
literal raw-input builder across all remaining empty clause rectangles of the
first scheduled Cook–Levin constraint. The predecessor retains the first
opportunity in the sixth fixed-width clause rectangle. This milestone walks
that rectangle and every later empty rectangle belonging to the same
constraint, emits no token, and stops at the separator that begins the second
scheduled constraint.

Let

```text
V = formulaVariableSlotBound
C = formulaTokensPerClause = 2 + (V + 4) * (V + 1)
Q = formulaClauseSlotsPerConstraint = 1 + V*V.
```

The predecessor coordinate is

```text
S6 = V + 1 + 5*C.
```

The number of remaining empty token opportunities is proved in both useful
forms:

```text
D = (V - 2) * (V + 2) * C
  = (Q - 5) * C.
```

The external polynomial is subtraction-free even though its evaluated
specification uses `V - 2`. The proof exposes positive time and tape factors
inside the existing variable-count polynomial and establishes the exact
evaluation in the kernel. The retained endpoint is

```text
S6 + D = V + 1 + Q*C.
```

That coordinate is the first token opportunity of the next constraint.

## Literal composition

The module composes `BuilderFifthClausePaddingRun.machine` with two generated
unary evaluators and the already-audited 25-rule
`BuilderFirstClausePaddingRun.PaddingCountdown.machine`:

1. `paddingPolynomial` materializes `D` in unary;
2. the countdown consumes one unit for every empty token opportunity; and
3. `secondConstraintStartPolynomial` materializes the absolute endpoint.

Three nested `WorkChain` boundaries contribute one literal nine-symbol bridge
each. The complete rule-count theorem is

```text
4432 + sixteen unary-evaluator ruleCount terms.
```

The constant is the predecessor's `4380`, the three new bridges, and the
reused 25-rule countdown table. Only the target evaluator's renamed accept and
reject states are global halts. `rules_pairwise_query_distinct` proves
collision-free first-match dispatch across every renamed table and bridge;
`rule_source_ne_acceptState` proves halt separation.

## Exact trace and schedule semantics

The module exposes exact evaluator, countdown, predecessor-prefix, launch, and
combined execution theorems. `workRunExact` starts from the literal raw input
tape, follows the composed finite rule table for the exact work-step count,
and reaches `finalConfiguration`. `finalTape_represents` proves that the raw
input representation is retained.

The schedule argument independently unfolds the first two shape constraints.
The first is the three-variable tape-symbol exactly-one constraint. Its first
four clause rectangles are populated; every later rectangle in its fixed
`Q`-slot allocation is empty. The next shape constraint is also exactly-one,
so its first populated clause begins with `Sep`. Consequently:

- `paddingSlot_direct_eq_padding` returns `some none` at every traversed
  coordinate;
- `secondConstraintStart_direct_eq_sep` returns
  `some (some CNFToken.sep)` at the endpoint;
- `specification_padding_run` emits the empty list for all `D` steps; and
- `specification_target_step` observes `Sep` and advances to the following
  coordinate.

The separator is observed but not emitted by this milestone. The machine's
formula output therefore remains exactly the complete fourth-clause prefix:

```text
T^FormulaWidth F
Sep T F T T F T T T F Finish
Sep F F F T F Finish
Sep F F F T T F Finish
Sep F T F F T T F Finish.
```

`finalTokenBits_eq_encodedFormula_fourthClause` identifies those bits with

```text
encodedFormula.take (2 * (FormulaWidth + 36)).
```

## External compiled bound

Let `R` be the evaluated root-prefix polynomial for `paddingPolynomial`. The
countdown satisfies

```text
countdownWorkSteps <= D * (2*R + 8) + D*D.
```

The external raw-transition polynomial evaluates to

```text
BuilderFifthClausePaddingRun.rawTimeBound(n)
+ 18
+ 6 * Unary.workSteps(paddingPolynomial, n)
+ 6 * (D * (2*R + 8) + D*D)
+ 6 * Unary.workSteps(secondConstraintStartPolynomial, n).
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
and endpoints, literal rule count, component and combined traces, the `Sep`
target, unchanged exact formula bits, retained input representation, compiled
acceptance, timeout boundaries, and the external polynomial evaluation.

```sh
lake env lean -DwarningAsError=true \
  lean-audit/PNPConcreteCookLevinBuilderFirstConstraintPaddingRunAxiomAudit.lean
lake env lean -DwarningAsError=true \
  lean-regression/PNPConcreteCookLevinBuilderFirstConstraintPaddingRun.lean
node --test \
  audits/lean-concrete-cook-levin-builder-first-constraint-padding-run0.test.mjs
```

The combined audit prints all 65 public declarations in the module and three
reused countdown interfaces. It accepts only the repository's approved
Lean-standard closure and rejects project axioms, `Classical.choice`, `sorry`,
`admit`, native or SAT shortcuts, host-side schedule lookup, caller-supplied
execution certificates, and theorem overclaims.

## Generated publication artifacts

The compiled environment records inventory coordinate
`PNP-LEAN-THEOREM-INVENTORY-2026-07-22-69`: 10,207 declarations, 5,600
theorems, 3,294 assumption-free theorems, 3,760 excluded private
declarations, 89 source-closure modules, and 1,445 reviewed milestone
candidates. The 7,367,905-byte canonical inventory SHA-256 is
`aa3ab0b201bee24ed42d4d8bd79cb9dde9ee9c1703c27710c25d64140037cf48`;
the Lean source-closure SHA-256 is
`a601805206f7106d4b226ae42906d17be8840e53817eb2b2e92aeeb06ae38a59`.

Publication map coordinate `PNP-FORMAL-PUBLICATION-MAP-2026-07-22-69` has
49 milestones, 46 earned milestones, three deliberately unearned global
milestones, and 1,445 exact kernel-type fingerprints. Its 440,764-byte file
SHA-256 is
`ef443dfe503b8ae85125f5297906fdfaf9fbadc95345cfaa1a10f5a4bba5a5da`;
its canonical reviewed-object fingerprint is
`9a106769643a49d8925bcab16e537260a0ee486d09b0ef7840f13b38d08a3d0f`.

Status coordinate `PNP-FORMAL-RECONSTRUCTION-STATUS-2026-07-22-69` is a
1,101,528-byte payload with SHA-256
`cfcf94f24f766bac34f4897fb5206f1bf6b721fa48d30ed3791b79423fbcec70`.
The generated report coordinate is
`PNP-CANONICAL-FORMAL-RECONSTRUCTION-REPORT-2026-07-22-69`; its 102,492-byte
TeX SHA-256 is
`47a53ff75a0f4691941e2879a863c719d2bd27d31b3114e813889a1bd504b3cb`,
and its 45-page, 357,765-byte PDF SHA-256 is
`ca3c506f0b0a100b3207e2e51f3670d1289128c43ebfa1d68ddc1a860a9d0ce4`.
All activation fingerprints remain unset and the concrete publication gate
remains false.

## Remaining boundary

This is one input-dependent traversal of the specifically proved empty suffix
of the first constraint rectangle, not a general dynamic formula cursor or
arbitrary raw slot decoder. It does not emit the second-constraint separator,
emit that constraint's first literal, traverse later constraints, finish the
formula builder, provide builder `RawRefinement` or a `PolynomialReduction`,
prove CNF-SAT NP-complete or in P, or establish `PNP.Main.p_eq_np`. The four
project assumptions, six blockers, unset activation fingerprints, and false
publication gate remain unchanged.
