# Concrete Cook–Levin second-clause prefix

`lean/PNP/Concrete/CookLevinBuilderSecondClausePrefix.lean` composes
the complete clause-two second-literal prefix with one selected `Finish`
token appender and one unary cursor advance. Every raw input therefore emits
the complete second clause and retains its first in-range padding coordinate.

The exact emitted token list is

```text
T^FormulaWidth F Sep T F T T F T T T F Finish Sep F F F T F Finish.
```

The machine observes but does not emit the following padding opportunity.

## Literal composition

`FinishTokenCursor.appender` reuses the complete 59-rule appender table with
its start state fixed to `CNFToken.finish`. A total nine-symbol bridge launches
the existing 45-rule cursor table, giving the fixed suffix

```text
59 + 9 + 45 = 113 rules.
```

A second total bridge places that suffix after
`BuilderSecondClauseSecondLiteralPrefix.machine`. The global symbolic rule
count is

```text
2098
+ width-evaluator ruleCount
+ body-start-coordinate evaluator ruleCount
+ first-literal-coordinate evaluator ruleCount
+ first-clause-coordinate evaluator ruleCount
+ remaining-padding evaluator ruleCount
+ second-clause-target evaluator ruleCount.
```

Only the cursor accept and reject images are global halts. The suffix and
global rule tables are pairwise query-distinct, so neither bridge nor either
renamed component can shadow another query.

## Exact trace and canonical output

`prefix_workRunExact` transports the predecessor trace.
`prefixFinish_launch_workStep` proves the outer symbol-preserving bridge.
`appender_workRunExact` appends exactly `Finish`, and
`finishTokenCursor_launch_workStep` launches the cursor table.
`cursor_workRunExact` performs the complete bidirectional unary scan.
`workRunExact` composes these facts into one exact all-input execution.

The independent schedule proof unfolds the first excluded-pair clause through
its terminator and first padding cell. Consequently:

- `secondClauseTokens_eq_canonical_formula_prefix` proves that the finite
  output is a prefix of `encodeCNFTokens problem.formula`;
- `finalTokenBits_eq_encodedFormula_secondClause` proves equality with
  `encodedFormula.take (2 * (FormulaWidth + 19))`;
- `clauseTerminatorSlot_direct_eq_finish` proves the executed opportunity is
  `Finish`; and
- `nextTokenSlot_direct_eq_padding` proves the retained opportunity is
  `some none`, not an out-of-range coordinate.

The retained coordinate is

```text
formulaVariableSlotBound + 1 + formulaTokensPerClause + 7.
```

For the empty input-only regression problem this coordinate is exactly
`105`. `finalTape_represents` preserves the raw input, while
`finalOutside_contains_finalTokenSlot` audits the unary coordinate retained
in the workspace.

## External compiled bound

The exact new work is one outer launch, one selected appender, one inner
launch, and one cursor scan. The external raw-transition polynomial evaluates
to

```text
BuilderSecondClauseSecondLiteralPrefix.rawTimeBound(n)
+ 390
+ 24*n
+ 12*FormulaWidth
+ 12*BuilderSecondClauseSeparatorStep.cursorWord.length.
```

`rawTimeBound_le` proves that this bounds six times the exact work trace.
The compiled interfaces prove exact execution, polynomial-fuel execution,
ordinary-start blank equivalence, acceptance, and non-timeout.

## Fail-closed boundaries and audits

The predecessor endpoint remains timeout before the outer launch, and the
successful appender endpoint remains timeout before the cursor launch.
Malformed tally and output symbols in the appender are globally stuck and
nonhalting. A malformed cursor scratch symbol enters the reviewed dead
self-loop. One-step-short total fuel also remains timeout.

The regression covers empty input, one-bit zero and one, odd and even lengths,
all-zero and all-one words, input-only and paired verifiers, the 113-rule
suffix and 2098-rule global base, both bridges, exact final tape and bits,
`Finish`, first padding, polynomial evaluation, compiled acceptance, and all
fail-closed boundaries.

```sh
lake env lean -DwarningAsError=true \
  lean-audit/PNPConcreteCookLevinBuilderSecondClausePrefixAxiomAudit.lean
lake env lean -DwarningAsError=true \
  lean-regression/PNPConcreteCookLevinBuilderSecondClausePrefix.lean
node --test \
  audits/lean-concrete-cook-levin-builder-second-clause-prefix0.test.mjs
```

The combined kernel audit covers all 55 public declarations plus the two
reviewed cursor dead-loop facts. Fifteen declarations have empty closure, ten
use only `propext`, and 32 use only `propext` and `Quot.sound`. No
declaration reaches a project axiom, `Classical.choice`, `sorry`, `admit`,
SAT/minimization code, host-side composition, or a caller-supplied execution
certificate.

## Generated publication artifacts

The compiled environment records inventory coordinate
`PNP-LEAN-THEOREM-INVENTORY-2026-07-19-56`, 8,473 declarations, 4,267
theorems, 3,013 assumption-free theorems, 76 source-closure modules, and 841
reviewed milestone candidates. Its canonical byte SHA-256 is
`37430f2e076d381bf8014f60a1caf7dee4ecbec518e7c792029892d75211dd0e`;
the Lean source-closure SHA-256 is
`bdc976391d9229224a6e006452af9aa6422a0ec2a5a40ae37e096e3b0b393f8e`.

Publication map coordinate `PNP-FORMAL-PUBLICATION-MAP-2026-07-19-56` has
36 milestones and 841 exact kernel-type fingerprints. Its exact file
SHA-256 is
`f842ba06fc032cc364ecb26405936b9cc40ed1dc2057b441db6335341d431412`,
and its canonical reviewed-object fingerprint is
`fb1b7eb3501795e43b1274796bff0ce147c18852ec694886c9a7e48a117125bd`.

Status coordinate `PNP-FORMAL-RECONSTRUCTION-STATUS-2026-07-19-56` has
SHA-256 `c1aaac5e815fbbbbdda2a1408b11ae11ee76740ec65e0d0b47049b2f32309339`.
The generated report coordinate is
`PNP-CANONICAL-FORMAL-RECONSTRUCTION-REPORT-2026-07-19-56`; its TeX SHA-256
is `893a8dbeb527e2dc281032f1a1ed0dce0780741f76c036e0d067ef285b8768d6`
and its 30-page, 321,299-byte PDF SHA-256 is
`2dbce8e8dd752da571b620b64911f87a6bf5d6e44e9fee05662fb13b97629c50`.
All activation fingerprints remain unset and the publication gate remains
false.

## Remaining boundary

This milestone completes only clause two. It advances once to the first
padding coordinate but does not traverse clause-two padding, reach the third
clause, implement an arbitrary dynamic formula cursor, emit the remaining
formula body, construct a complete raw formula builder, provide builder
`RawRefinement` or a `PolynomialReduction`, prove CNF-SAT NP-complete or in
P, or establish `PNP.Main.p_eq_np`. The four project assumptions, six
blockers, unset activation fingerprints, and false publication gate remain
unchanged.
