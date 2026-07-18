# Concrete Cook–Levin second-clause second-literal prefix

`lean/PNP/Concrete/CookLevinBuilderSecondClauseSecondLiteralPrefix.lean`
composes the complete clause-two first-literal prefix with selected `F`, `T`,
and `F` token appenders and one unary cursor advance after each token. Every
raw input therefore emits the complete negative literal on variable one in
clause two and retains the coordinate of the following clause terminator.

The exact emitted token list is

```text
T^FormulaWidth F Sep T F T T F T T T F Finish Sep F F F T F.
```

The final four populated opportunities are proved independently: the second
literal has sign `F`, unary unit `T`, and terminator `F`, while the next direct
token is `Finish`. The machine emits the first three and observes, but does
not emit, the clause terminator.

## Literal composition

`TrueTokenCursor.appender` reuses the complete 59-rule token appender with its
start state fixed to the `T` request. Nine total symbol-preserving rules
launch the existing 45-rule cursor table, so that component has exactly

```text
59 + 9 + 45 = 113 rules.
```

`TrueFalseSuffix.machine` places that component before the existing selected
`F` token/cursor component:

```text
113 + 9 + 113 = 235 rules.
```

`SecondLiteralSuffix.machine` places another selected `F` token/cursor
component before that tail:

```text
113 + 9 + 235 = 357 rules.
```

The outer machine places the complete suffix after
`BuilderSecondClauseFirstLiteralPrefix.machine` behind one more total bridge.
Its symbolic rule count is

```text
1976
+ width-evaluator ruleCount
+ body-start-coordinate evaluator ruleCount
+ first-literal-coordinate evaluator ruleCount
+ first-clause-coordinate evaluator ruleCount
+ remaining-padding evaluator ruleCount
+ second-clause-target evaluator ruleCount.
```

Only the terminator cursor supplies the global accept and reject images.
Every component and the global table is pairwise query-distinct, so no bridge
or renamed table can shadow another first-match query.

## Exact trace, output, and schedule

The proof exposes exact runs for all three appenders and cursor advances, plus
all six launches: predecessor to suffix, each appender to its cursor, sign
cursor to the unary tail, and unary cursor to the terminator component.
`workRunExact` composes them into one all-input trace from the ordinary raw
input work tape to the global accepting configuration.

The independent schedule proof unfolds the first excluded-pair clause far
enough to identify its second witness as variable one. Consequently:

- `secondClauseSecondLiteralTokens_eq_canonical_formula_prefix` proves the
  finite output is a prefix of `encodeCNFTokens problem.formula`;
- `finalTokenBits_eq_encodedFormula_secondClauseSecondLiteral` proves exact
  equality with `encodedFormula.take (2 * (FormulaWidth + 18))`;
- `secondLiteralSignSlot_direct_eq_f` proves the negative sign;
- `secondLiteralUnaryUnitSlot_direct_eq_t` proves the unary-one unit;
- `secondLiteralTerminatorSlot_direct_eq_f` proves its terminator; and
- `nextTokenSlot_direct_eq_finish` proves the retained clause terminator.

The retained coordinate is

```text
formulaVariableSlotBound + 1 + formulaTokensPerClause + 6.
```

`finalTape_represents` preserves the raw input, and
`finalOutside_contains_finalTokenSlot` audits that coordinate in the unary
workspace.

## External compiled bound

The exact work count consists of the predecessor trace, six bridge steps,
three selected appenders, and three cursor scans. The external raw-transition
polynomial evaluates to

```text
BuilderSecondClauseFirstLiteralPrefix.rawTimeBound(n)
+ 1026
+ 72*n
+ 36*FormulaWidth
+ 36*BuilderSecondClauseSeparatorStep.cursorWord.length.
```

`rawTimeBound_le` proves that polynomial bounds six times the exact work
trace. The compiled interfaces prove exact execution, polynomial-fuel
execution, ordinary-start blank equivalence, acceptance, and non-timeout.

## Fail-closed boundaries and audits

The exact raw-input execution remains `timeout` at all six pre-launch
boundaries: the predecessor endpoint; the sign appender and cursor endpoints;
the unary appender and cursor endpoints; and the terminator appender endpoint.
A malformed tally or output symbol in any appender cannot reach a global
halt. A malformed scratch symbol in any cursor enters the reviewed nonhalting
dead loop. One-step-short total fuel also remains `timeout`.

The regression covers empty input, one-bit zero and one, odd and even lengths,
all-zero and all-one inputs, input-only and paired verifiers, exact rules and
coordinates, all six launches, exact final tape and formula bits, all four
direct token outcomes, polynomial evaluation, compiled acceptance, and every
fail-closed boundary.

```sh
lake env lean -DwarningAsError=true \
  lean-audit/PNPConcreteCookLevinBuilderSecondClauseSecondLiteralPrefixAxiomAudit.lean
lake env lean -DwarningAsError=true \
  lean-regression/PNPConcreteCookLevinBuilderSecondClauseSecondLiteralPrefix.lean
node --test \
  audits/lean-concrete-cook-levin-builder-second-clause-second-literal-prefix0.test.mjs
```

The combined kernel audit covers all 113 public declarations in the module
plus the two reviewed cursor dead-loop facts used for malformed-scratch fail
closure: 34 declarations have empty closure, 25 use only `propext`, and 56
use only `propext` and `Quot.sound`. No declaration reaches a project axiom,
`Classical.choice`, `sorry`, `admit`, SAT/minimization code, host-side
composition, or a caller-supplied execution certificate.

## Generated publication artifacts

The compiled environment records inventory coordinate
`PNP-LEAN-THEOREM-INVENTORY-2026-07-18-55`, 8,387 declarations, 4,198
theorems, 2,998 assumption-free theorems, 75 source-closure modules, and 802
reviewed milestone candidates. Its canonical byte SHA-256 is
`4f851b46d3b725fb042dc2bb5b85a790a098201aeb67b465e3956f533ee8e7fa`;
the Lean source-closure SHA-256 is
`21351939972f87bd69b37fb282a966a60674b3cb2c2a2615ab6529b53e1ea0ba`.

Publication map coordinate `PNP-FORMAL-PUBLICATION-MAP-2026-07-18-55` has
35 milestones and 802 exact kernel-type fingerprints. Its exact file
SHA-256 is
`4e0b23c76921df26bd047a84666bf9b66d87439a18fe0df745d4cccdd21e1b29`,
and its canonical reviewed-object fingerprint is
`12cd4ea4f76edd3ce72b655d70779113f0193af3c5c32b240d99cc81276508cb`.

Status coordinate `PNP-FORMAL-RECONSTRUCTION-STATUS-2026-07-18-55` has
SHA-256 `54a514028f7f25bf3ab47a0f881d8c9299d50d749039d7727ceae79b7894dd03`.
The generated report coordinate is
`PNP-CANONICAL-FORMAL-RECONSTRUCTION-REPORT-2026-07-18-55`; its TeX SHA-256
is `ddec0003b2b15374b9f4150ad13f346170738fbc1daf2991a8a82690b1536fbb`
and its 29-page, 319,057-byte PDF SHA-256 is
`40b6e6a220e55fea83c13f631a1ec4a97531f782184290d97dced0a81f170c7b`.
All activation fingerprints remain unset and the publication gate remains
false.

## Remaining boundary

This is one fixed negative literal and three unary cursor advances. It does
not emit the clause terminator, complete clause two, implement an arbitrary
dynamic formula cursor, build the remaining formula body, construct a
complete raw formula builder, provide builder `RawRefinement` or a
`PolynomialReduction`, prove CNF-SAT NP-complete or in P, or establish
`PNP.Main.p_eq_np`. The four project assumptions, six blockers, unset
activation fingerprints, and false publication gate remain unchanged.
