# Concrete Cook–Levin third-clause first-literal prefix

`lean/PNP/Concrete/CookLevinBuilderThirdClauseFirstLiteralPrefix.lean`
composes the complete raw-input-through-third-clause-separator machine with
two selected `F` token appenders and two copies of the existing unary cursor
advance. Every raw input therefore emits the complete negative literal on
variable zero in clause three and retains the coordinate of the following
literal sign.

The exact emitted token list is

```text
T^FormulaWidth F
Sep T F T T F T T T F Finish
Sep F F F T F Finish
Sep F F.
```

The final three populated opportunities in this prefix are independently
proved to be `F`: the negative sign, the unary-zero terminator, and the sign
of the next negative literal on variable two. The machine emits the first two
of those opportunities. It does not emit the following `F`.

## Literal composition

`BuilderSecondClauseFirstLiteralPrefix.FalseTokenCursor.appender` reuses the
complete 59-rule token appender with
its start state fixed to the `F` request. Nine total symbol-preserving rules
launch the existing 45-rule cursor table, so one component has exactly

```text
59 + 9 + 45 = 113 rules.
```

`BuilderSecondClauseFirstLiteralPrefix.FirstLiteralSuffix.machine` is reused
unchanged. It contains two collision-free renamed copies of that component
and a second total nine-rule bridge:

```text
113 + 9 + 113 = 235 rules.
```

The outer machine places the suffix after
`BuilderThirdClauseSeparatorStep.machine` behind one more total bridge. Its
complete symbolic rule count is

```text
2516
+ width-evaluator ruleCount
+ body-start-coordinate evaluator ruleCount
+ first-literal-coordinate evaluator ruleCount
+ first-clause-coordinate evaluator ruleCount
+ first-clause-padding evaluator ruleCount
+ second-clause-target evaluator ruleCount
+ second-clause-padding evaluator ruleCount
+ third-clause-target evaluator ruleCount.
```

Only the second cursor copy supplies the global accept and reject images.
Every component and the global table is pairwise query-distinct, so no bridge
or renamed table can shadow another first-match query.

## Exact trace, output, and schedule

The proof exposes exact runs for both appenders and both cursor advances, plus
the four literal bridge transitions: predecessor to suffix, first appender to
first cursor, first cursor to second appender, and second appender to second
cursor. `workRunExact` composes them into one all-input trace from the ordinary
raw-input work tape to the global accepting configuration.

The independent schedule proof unfolds the first three shape clauses and
identifies the third excluded pair as variables zero and two. Consequently:

- `thirdClauseFirstLiteralTokens_eq_canonical_formula_prefix` proves the
  finite output is a prefix of `encodeCNFTokens problem.formula`;
- `finalTokenBits_eq_encodedFormula_thirdClauseFirstLiteral` proves exact
  equality with `encodedFormula.take (2 * (FormulaWidth + 22))`;
- `firstLiteralSignSlot_direct_eq_f` proves the negative sign;
- `firstLiteralZeroTerminatorSlot_direct_eq_f` proves the unary-zero
  terminator; and
- `nextTokenSlot_direct_eq_f` proves the retained next-literal coordinate.

The final retained coordinate is

```text
formulaVariableSlotBound + 1 + 2 * formulaTokensPerClause + 3.
```

`finalTape_represents` preserves the raw input and
`finalOutside_contains_finalTokenSlot` audits that coordinate in the unary
workspace.

## External compiled bound

The exact work count consists of the predecessor trace, four bridge steps,
two selected appenders, and two cursor scans. The external raw-transition
polynomial evaluates to

```text
BuilderThirdClauseSeparatorStep.rawTimeBound(n)
+ 732
+ 48*n
+ 24*FormulaWidth
+ 24*BuilderThirdClauseSeparatorStep.cursorWord.length.
```

`rawTimeBound_le` proves that polynomial bounds six times the exact work
trace. The compiled interfaces prove exact execution, polynomial-fuel
execution, ordinary-start blank equivalence, acceptance, and non-timeout.

## Fail-closed boundaries and audits

The exact raw-input execution remains `timeout` at all four pre-launch
boundaries: the predecessor endpoint, the first appender endpoint, the first
cursor endpoint, and the second appender endpoint. A malformed tally or
output symbol in either appender cannot reach a global halt. A malformed
scratch symbol in either cursor enters the reviewed nonhalting dead loop.
One-step-short total fuel also remains `timeout`.

The regression covers empty input, one-bit zero and one, odd and even lengths,
all-zero and all-one inputs, input-only and paired verifiers, exact rules and
coordinates, all four launches, exact final tape and formula bits, the three
direct `F` outcomes, polynomial evaluation, compiled acceptance, and every
fail-closed boundary.

```sh
lake env lean -DwarningAsError=true \
  lean-audit/PNPConcreteCookLevinBuilderThirdClauseFirstLiteralPrefixAxiomAudit.lean
lake env lean -DwarningAsError=true \
  lean-regression/PNPConcreteCookLevinBuilderThirdClauseFirstLiteralPrefix.lean
node --test \
  audits/lean-concrete-cook-levin-builder-third-clause-first-literal-prefix0.test.mjs
```

The combined kernel audit covers all 74 public declarations in the module,
the eleven reviewed interfaces of the reused suffix, and the two cursor
dead-loop facts used to prove malformed-scratch fail closure. Of those 87
declarations, 25 have empty closure, 18 use only `propext`, and 44 use only
`propext` and `Quot.sound`. No declaration reaches a project
axiom, `Classical.choice`,
`sorry`, `admit`, SAT/minimization code, host-side composition, or a
caller-supplied execution certificate.

## Generated publication artifacts

The compiled environment records inventory coordinate
`PNP-LEAN-THEOREM-INVENTORY-2026-07-19-59`, 8,811 declarations, 4,530
theorems, 3,062 assumption-free theorems, 79 source-closure modules, and 960
reviewed milestone candidates. Its canonical byte SHA-256 is
`36c617c6996762de308df36c98c10befa5f9135d354dc91dee589dafb79bf697`;
the Lean source-closure SHA-256 is
`49d0e1f95d163c3ae68ba9e8e8234bf8af77f67e7f692b41f292dfceba3a0eb3`.

Publication map coordinate `PNP-FORMAL-PUBLICATION-MAP-2026-07-19-59` has
39 milestones and 960 exact kernel-type fingerprints. Its exact file
SHA-256 is
`91aa2f445c37dce20c473eb223210e0b85e11ae26edc2d29c14c9049fae40835`,
and its canonical reviewed-object fingerprint is
`054bb1f0d98730b7cc744fc4a47f43eb4e37a07c16ca26f7676a5eaa4bfb55a6`.

Status coordinate `PNP-FORMAL-RECONSTRUCTION-STATUS-2026-07-19-59` has
SHA-256 `f62e3d42cf1421458246c7b9872f378802d90ea7981879cebbc30ec5862e4376`.
The generated report coordinate is
`PNP-CANONICAL-FORMAL-RECONSTRUCTION-REPORT-2026-07-19-59`; its 75,000-byte
TeX SHA-256 is `225e40124754cc57595ca400eeb355ef2393a10df351077381fe3eea2290ce61`
and its 34-page, 330,268-byte PDF SHA-256 is
`020d7868dd177bc116d453b9eb3b52f1096a8bb8e10305603ce77c2ceddb3568`.
All activation fingerprints remain unset and the publication gate remains
false.

## Remaining boundary

This is one fixed negative literal and two unary cursor advances. It does not
complete clause three, emit the following `F`, implement an arbitrary dynamic
formula cursor, build the remaining formula body, construct a complete raw
formula builder, provide builder `RawRefinement` or a `PolynomialReduction`,
prove CNF-SAT NP-complete or in P, or establish `PNP.Main.p_eq_np`. The four
project assumptions, six blockers, unset activation fingerprints, and false
publication gate remain unchanged.
