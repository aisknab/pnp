# Concrete Cook–Levin third-clause second-literal prefix

`lean/PNP/Concrete/CookLevinBuilderThirdClauseSecondLiteralPrefix.lean`
composes the complete raw-input-through-third-clause-first-literal machine
with the fixed token sequence `F T T F`. Each token appender is followed by
the existing bidirectional unary cursor advance. Every raw input therefore
emits the complete negative literal on variable two in clause three and
retains the coordinate of the following clause terminator.

The exact emitted token list is

```text
T^FormulaWidth F
Sep T F T T F T T T F Finish
Sep F F F T F Finish
Sep F F F T T F.
```

The machine does not emit the following clause terminator.

## Literal composition

The selected `F` and `T` components each contain the complete 59-rule token
appender, nine total symbol-preserving launch rules, and the existing 45-rule
cursor table:

```text
59 + 9 + 45 = 113 rules.
```

The nested suffix tables are literal finite compositions:

```text
TrueFalseSuffix       = 113 + 9 + 113 = 235 rules
TrueTrueFalseSuffix   = 113 + 9 + 235 = 357 rules
SecondLiteralSuffix  = 113 + 9 + 357 = 479 rules.
```

One final total nine-rule bridge follows
`BuilderThirdClauseFirstLiteralPrefix.machine`. The complete symbolic rule
count is

```text
3004
+ width-evaluator ruleCount
+ body-start-coordinate evaluator ruleCount
+ first-literal-coordinate evaluator ruleCount
+ first-clause-coordinate evaluator ruleCount
+ first-clause-padding evaluator ruleCount
+ second-clause-target evaluator ruleCount
+ second-clause-padding evaluator ruleCount
+ third-clause-target evaluator ruleCount.
```

Only the final cursor component supplies the global accept and reject images.
Every component and the global table is pairwise query-distinct, so no bridge
or renamed table shadows another first-match query.

## Exact trace, output, and schedule

The proof exposes exact runs for all four appenders and cursor advances, all
four appender-to-cursor launches, the three internal suffix launches, and the
outer predecessor launch. `workRunExact` composes those phases into one
all-input trace from the ordinary raw-input work tape to the global accepting
configuration.

The independent schedule proof unfolds the first three shape clauses and
constructively identifies the third excluded pair as variables zero and two.
Consequently:

- `thirdClauseSecondLiteralTokens_eq_canonical_formula_prefix` proves the
  finite output is a prefix of `encodeCNFTokens problem.formula`;
- `finalTokenBits_eq_encodedFormula_thirdClauseSecondLiteral` proves exact
  equality with `encodedFormula.take (2 * (FormulaWidth + 26))`;
- the direct-slot theorems prove the second literal is exactly `F T T F`; and
- `nextTokenSlot_direct_eq_finish` proves the retained coordinate contains
  `Finish`.

The retained coordinate is

```text
formulaVariableSlotBound + 1 + 2 * formulaTokensPerClause + 7.
```

`finalTape_represents` preserves the raw input, and
`finalOutside_contains_finalTokenSlot` audits that coordinate in the unary
workspace.

## External compiled bound

The exact work count adds eight bridge steps, four selected appenders, and
four cursor scans to the predecessor trace. The external raw-transition
polynomial evaluates to

```text
BuilderThirdClauseFirstLiteralPrefix.rawTimeBound(n)
+ 1752
+ 96*n
+ 48*FormulaWidth
+ 48*BuilderThirdClauseSeparatorStep.cursorWord.length.
```

`rawTimeBound_le` proves this polynomial bounds six times the exact work
trace. The compiled interfaces prove exact execution, polynomial-fuel
execution, ordinary-start blank equivalence, acceptance, and non-timeout.

## Fail-closed boundaries and audits

The exact raw-input execution remains `timeout` at all eight pre-launch
boundaries: the predecessor endpoint, each of four appender endpoints, and
the first three cursor endpoints. A malformed tally or output symbol in any
appender is stuck outside the global halts. A malformed scratch symbol in any
cursor enters the reviewed nonhalting dead loop. One-step-short total fuel
also remains `timeout`.

The regression covers empty input, one-bit zero and one, odd and even lengths,
all-zero and all-one inputs, input-only and paired verifiers, exact rule
counts and coordinates, exact bridge launches, exact final tape and formula
bits, all five direct schedule outcomes, polynomial evaluation, compiled
acceptance, malformed workspaces, pre-launch endpoints, and one-step-short
fuel.

```sh
lake env lean -DwarningAsError=true \
  lean-audit/PNPConcreteCookLevinBuilderThirdClauseSecondLiteralPrefixAxiomAudit.lean
lake env lean -DwarningAsError=true \
  lean-regression/PNPConcreteCookLevinBuilderThirdClauseSecondLiteralPrefix.lean
node --test \
  audits/lean-concrete-cook-levin-builder-third-clause-second-literal-prefix0.test.mjs
```

The kernel audit covers all 145 public declarations in the module. Exactly
46 have empty closure, 32 use only `propext`, and 67 use only `propext` and
`Quot.sound`. No declaration reaches a project axiom, `Classical.choice`,
`sorry`, `admit`, SAT/minimization code, host-side composition, or a
caller-supplied execution certificate.

## Generated publication artifacts

The compiled environment records inventory coordinate
`PNP-LEAN-THEOREM-INVENTORY-2026-07-20-60`, 9,024 declarations, 4,688
theorems, 3,108 assumption-free theorems, 80 source-closure modules, and
1,050 reviewed milestone candidates. Its canonical byte SHA-256 is
`d03df5df6a48f11abc39ec6bb2905f5527125b8cba04fbd8bd513a151b31c5f3`;
the Lean source-closure SHA-256 is
`9a711cfc0c85aea0ef04efaf16a885e38f14a98831874c81b5cc889a5ef3715e`.

Publication map coordinate `PNP-FORMAL-PUBLICATION-MAP-2026-07-20-60` has
40 milestones and 1,050 exact kernel-type fingerprints. Its exact file
SHA-256 is
`041eef6821e839f112579c0adfa33a411f8a92e72487579a069fdde241275c78`,
and its canonical reviewed-object fingerprint is
`45019958363732c256a7b806333e74c909c3c726325742a9ed5c2d4aa852c67c`.

Status coordinate `PNP-FORMAL-RECONSTRUCTION-STATUS-2026-07-20-60` has
SHA-256 `e83699a5cbf2fa394028452f828fd7696c1026367d78ce8dfe222967ce73c887`.
The generated report coordinate is
`PNP-CANONICAL-FORMAL-RECONSTRUCTION-REPORT-2026-07-20-60`; its 78,034-byte
TeX SHA-256 is `89cfa13fc24e6478be0c286e2488f99096e9c9bc000afe10265377e0df92133a`
and its 35-page, 332,633-byte PDF SHA-256 is
`03794ad01a4dccb138606b09bfa7dd449f81b301101f8198264060f96d29a72c`.
All activation fingerprints remain unset and the publication gate remains
false.

## Remaining boundary

This milestone emits one fixed negative literal and performs four cursor
advances. It does not emit the following `Finish`, complete clause three,
implement an arbitrary dynamic formula cursor, build the remaining formula
body, construct a complete raw formula builder, provide builder
`RawRefinement` or a `PolynomialReduction`, prove CNF-SAT NP-complete or in P,
or establish `PNP.Main.p_eq_np`. The four project assumptions, six blockers,
unset activation fingerprints, and false publication gate remain unchanged.
