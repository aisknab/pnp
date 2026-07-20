# Concrete Cook–Levin third-clause prefix

`lean/PNP/Concrete/CookLevinBuilderThirdClausePrefix.lean` composes
the complete clause-three second-literal prefix with one selected `Finish`
token appender and one unary cursor advance. Every raw input therefore emits
the complete third clause and retains its first in-range padding coordinate.

The exact emitted token list is

```text
T^FormulaWidth F
Sep T F T T F T T T F Finish
Sep F F F T F Finish
Sep F F F T T F Finish
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
`BuilderThirdClauseSecondLiteralPrefix.machine`. The global symbolic rule
count is

```text
3126
+ width-evaluator ruleCount
+ body-start-coordinate evaluator ruleCount
+ first-literal-coordinate evaluator ruleCount
+ first-clause-coordinate evaluator ruleCount
+ first-clause remaining-padding evaluator ruleCount
+ second-clause-target evaluator ruleCount
+ second-clause remaining-padding evaluator ruleCount
+ third-clause-target evaluator ruleCount.
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

The independent schedule proof unfolds the first three canonical clauses
through the third terminator and its first padding cell. Consequently:

- `thirdClauseTokens_eq_canonical_formula_prefix` proves that the finite
  output is a prefix of `encodeCNFTokens problem.formula`;
- `finalTokenBits_eq_encodedFormula_thirdClause` proves equality with
  `encodedFormula.take (2 * (FormulaWidth + 27))`;
- `clauseTerminatorSlot_direct_eq_finish` proves the executed opportunity is
  `Finish`; and
- `nextTokenSlot_direct_eq_padding` proves the retained opportunity is
  `some none`, not an out-of-range coordinate.

The retained coordinate is

```text
formulaVariableSlotBound + 1 + 2*formulaTokensPerClause + 8.
```

For the empty input-only regression problem this coordinate is exactly
`196`. `finalTape_represents` preserves the raw input, while
`finalOutside_contains_finalTokenSlot` audits the unary coordinate retained
in the workspace.

## External compiled bound

The exact new work is one outer launch, one selected appender, one inner
launch, and one cursor scan. The external raw-transition polynomial evaluates
to

```text
BuilderThirdClauseSecondLiteralPrefix.rawTimeBound(n)
+ 498
+ 24*n
+ 12*FormulaWidth
+ 12*BuilderThirdClauseSeparatorStep.cursorWord.length.
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
suffix and 3126-rule global base, both bridges, exact final tape and bits,
`Finish`, first padding, polynomial evaluation, compiled acceptance, and all
fail-closed boundaries.

```sh
lake env lean -DwarningAsError=true \
  lean-audit/PNPConcreteCookLevinBuilderThirdClausePrefixAxiomAudit.lean
lake env lean -DwarningAsError=true \
  lean-regression/PNPConcreteCookLevinBuilderThirdClausePrefix.lean
node --test \
  audits/lean-concrete-cook-levin-builder-third-clause-prefix0.test.mjs
```

The combined kernel audit covers all 55 public declarations plus the two
reviewed cursor dead-loop facts. Fourteen declarations have empty closure, ten
use only `propext`, and 33 use only `propext` and `Quot.sound`. No
declaration reaches a project axiom, `Classical.choice`, `sorry`, `admit`,
SAT/minimization code, host-side composition, or a caller-supplied execution
certificate.

## Generated publication artifacts

The compiled environment records inventory coordinate
`PNP-LEAN-THEOREM-INVENTORY-2026-07-20-61`, 9,117 declarations, 4,764
theorems, 3,122 assumption-free theorems, 81 source-closure modules, and 1,089
reviewed milestone candidates. Its canonical byte SHA-256 is
`155a862474126aa8fb8c5c75c6e2e7126f1b69febac1e4100d505e405d974db5`;
the Lean source-closure SHA-256 is
`0d09467c09dbdd99b07c0fea2f21e24d75b9efc4701c6d5c6e3102a913cba0c8`.

Publication map coordinate `PNP-FORMAL-PUBLICATION-MAP-2026-07-20-61` has
41 milestones and 1,089 exact kernel-type fingerprints. Its exact file
SHA-256 is
`c931f62bdc480c02a1a2c3556fbb480999a653282282ff0ecc5558a5f283659e`,
and its canonical reviewed-object fingerprint is
`cd34ccfe2634eea66b4e9f0f21e04a542624cd240fe2ed11f9072b879cc9fb71`.

Status coordinate `PNP-FORMAL-RECONSTRUCTION-STATUS-2026-07-20-61` has
SHA-256 `8cce5744e3f8a1f5a0f9119bea2034c5afad1685c9b6f8bcbdb9939baeb9a09b`.
The generated report coordinate is
`PNP-CANONICAL-FORMAL-RECONSTRUCTION-REPORT-2026-07-20-61`; its 79,940-byte
TeX SHA-256 is `0d6d5d3270c20f985bd137016a572fc89c7fb95621c2a3008adc9f0b2e3b029d`
and its 36-page, 334,685-byte PDF SHA-256 is
`2ea1b5b4f789fbdc8fa8c3fadf0c1370d10b1aa415340a711829e9aed271972c`.
All activation fingerprints remain unset and the publication gate remains
false.

## Remaining boundary

This milestone completes only clause three. It advances once to the first
padding coordinate but does not traverse clause-three padding, implement an
arbitrary dynamic formula cursor, emit the remaining
formula body, construct a complete raw formula builder, provide builder
`RawRefinement` or a `PolynomialReduction`, prove CNF-SAT NP-complete or in
P, or establish `PNP.Main.p_eq_np`. The four project assumptions, six
blockers, unset activation fingerprints, and false publication gate remain
unchanged.
