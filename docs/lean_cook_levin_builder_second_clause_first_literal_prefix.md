# Concrete Cook–Levin second-clause first-literal prefix

`lean/PNP/Concrete/CookLevinBuilderSecondClauseFirstLiteralPrefix.lean`
composes the complete raw-input-through-second-clause-separator machine with
two selected `F` token appenders and two copies of the existing unary cursor
advance. Every raw input therefore emits the complete negative literal on
variable zero in clause two and retains the coordinate of the following
literal sign.

The exact emitted token list is

```text
T^FormulaWidth F Sep T F T T F T T T F Finish Sep F F.
```

The final three populated opportunities in this prefix are independently
proved to be `F`: the negative sign, the unary-zero terminator, and the sign
of the next negative literal on variable one. The machine emits the first two
of those opportunities. It observes but does not emit the third.

## Literal composition

`FalseTokenCursor.appender` reuses the complete 59-rule token appender with
its start state fixed to the `F` request. Nine total symbol-preserving rules
launch the existing 45-rule cursor table, so one component has exactly

```text
59 + 9 + 45 = 113 rules.
```

`FirstLiteralSuffix.machine` contains two collision-free renamed copies of
that component and a second total nine-rule bridge:

```text
113 + 9 + 113 = 235 rules.
```

The outer machine places the suffix after
`BuilderSecondClauseSeparatorStep.machine` behind one more total bridge. Its
complete symbolic rule count is

```text
1610
+ width-evaluator ruleCount
+ body-start-coordinate evaluator ruleCount
+ first-literal-coordinate evaluator ruleCount
+ first-clause-coordinate evaluator ruleCount
+ remaining-padding evaluator ruleCount
+ second-clause-target evaluator ruleCount.
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

The independent schedule proof unfolds the first excluded-pair clause far
enough to identify its witnesses as variables zero and one. Consequently:

- `secondClauseFirstLiteralTokens_eq_canonical_formula_prefix` proves the
  finite output is a prefix of `encodeCNFTokens problem.formula`;
- `finalTokenBits_eq_encodedFormula_secondClauseFirstLiteral` proves exact
  equality with `encodedFormula.take (2 * (FormulaWidth + 15))`;
- `firstLiteralSignSlot_direct_eq_f` proves the negative sign;
- `firstLiteralZeroTerminatorSlot_direct_eq_f` proves the unary-zero
  terminator; and
- `nextTokenSlot_direct_eq_f` proves the retained next-literal coordinate.

The final retained coordinate is

```text
formulaVariableSlotBound + 1 + formulaTokensPerClause + 3.
```

`finalTape_represents` preserves the raw input and
`finalOutside_contains_finalTokenSlot` audits that coordinate in the unary
workspace.

## External compiled bound

The exact work count consists of the predecessor trace, four bridge steps,
two selected appenders, and two cursor scans. The external raw-transition
polynomial evaluates to

```text
BuilderSecondClauseSeparatorStep.rawTimeBound(n)
+ 564
+ 48*n
+ 24*FormulaWidth
+ 24*BuilderSecondClauseSeparatorStep.cursorWord.length.
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
  lean-audit/PNPConcreteCookLevinBuilderSecondClauseFirstLiteralPrefixAxiomAudit.lean
lake env lean -DwarningAsError=true \
  lean-regression/PNPConcreteCookLevinBuilderSecondClauseFirstLiteralPrefix.lean
node --test \
  audits/lean-concrete-cook-levin-builder-second-clause-first-literal-prefix0.test.mjs
```

The combined kernel audit covers all 85 public declarations in the module
plus the two reviewed cursor dead-loop facts used to prove malformed-scratch
fail closure: 25 declarations have empty closure, 18 use only `propext`, and
44 use only `propext` and `Quot.sound`. No declaration reaches a project
axiom, `Classical.choice`,
`sorry`, `admit`, SAT/minimization code, host-side composition, or a
caller-supplied execution certificate.

## Generated publication artifacts

The compiled environment records inventory coordinate
`PNP-LEAN-THEOREM-INVENTORY-2026-07-18-54`, 8,229 declarations, 4,080
theorems, 2,964 assumption-free theorems, 74 source-closure modules, and 729
reviewed milestone candidates. Its canonical byte SHA-256 is
`6c63d3f093aa136560154ce1340abc75884da199dee1867c14550e95f6a3c268`;
the Lean source-closure SHA-256 is
`59d1daa0e4497cc46fdc2f5d7013cbbcc87b57a3f2b8de70638ce79f9e2f3b63`.

Publication map coordinate `PNP-FORMAL-PUBLICATION-MAP-2026-07-18-54` has
34 milestones and 729 exact kernel-type fingerprints. Its exact file
SHA-256 is
`c28eb555971c107280ee393d7ffa204bab1aab2fc2a5e0e6ae7e4830e16803dd`,
and its canonical reviewed-object fingerprint is
`19c643af7cea8647a6a35e8f677300a8a993178a93a390063498697973c7b34b`.

Status coordinate `PNP-FORMAL-RECONSTRUCTION-STATUS-2026-07-18-54` has
SHA-256 `3e0ff0851a3140c20f8ca8ec2eaa51e1dc99c8f45af82f54bb67115201f1fe6b`.
The generated report coordinate is
`PNP-CANONICAL-FORMAL-RECONSTRUCTION-REPORT-2026-07-18-54`; its TeX SHA-256
is `21fbcfd4746d5bbdd64c3a33227f5e0748690c4285e681d25cc9448b3a1b612e`
and its 28-page, 317,210-byte PDF SHA-256 is
`961a0bb61fc5e69bb28250f8fd265023aa2a949093ff6c6abd46707ba822c74b`.
All activation fingerprints remain unset and the publication gate remains
false.

## Remaining boundary

This is one fixed negative literal and two unary cursor advances. It does not
complete clause two, emit the following `F`, implement an arbitrary dynamic
formula cursor, build the remaining formula body, construct a complete raw
formula builder, provide builder `RawRefinement` or a `PolynomialReduction`,
prove CNF-SAT NP-complete or in P, or establish `PNP.Main.p_eq_np`. The four
project assumptions, six blockers, unset activation fingerprints, and false
publication gate remain unchanged.
