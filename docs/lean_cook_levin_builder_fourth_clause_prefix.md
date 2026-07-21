# Concrete Cook–Levin fourth-clause prefix

`lean/PNP/Concrete/CookLevinBuilderFourthClausePrefix.lean` composes
the complete clause-four second-literal prefix with one selected `Finish`
token appender and one unary cursor advance. Every raw input therefore emits
the complete fourth clause and retains its first in-range padding coordinate.

The exact emitted token list is

```text
T^FormulaWidth F
Sep T F T T F T T T F Finish
Sep F F F T F Finish
Sep F F F T T F Finish
Sep F T F F T T F Finish
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
`BuilderFourthClauseSecondLiteralPrefix.machine`. The global symbolic rule
count is

```text
4276
+ width-evaluator ruleCount
+ body-start-coordinate evaluator ruleCount
+ first-literal-coordinate evaluator ruleCount
+ first-clause-coordinate evaluator ruleCount
+ first-clause remaining-padding evaluator ruleCount
+ second-clause-target evaluator ruleCount
+ second-clause remaining-padding evaluator ruleCount
+ third-clause-target evaluator ruleCount
+ third-clause remaining-padding evaluator ruleCount
+ fourth-clause-target evaluator ruleCount.
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

The independent schedule proof unfolds the first four canonical clauses
through the fourth terminator and its first padding cell. Consequently:

- `fourthClauseTokens_eq_canonical_formula_prefix` proves that the finite
  output is a prefix of `encodeCNFTokens problem.formula`;
- `finalTokenBits_eq_encodedFormula_fourthClause` proves equality with
  `encodedFormula.take (2 * (FormulaWidth + 36))`;
- `clauseTerminatorSlot_direct_eq_finish` proves the executed opportunity is
  `Finish`; and
- `nextTokenSlot_direct_eq_padding` proves the retained opportunity is
  `some none`, not an out-of-range coordinate.

The retained coordinate is

```text
formulaVariableSlotBound + 1 + 3*formulaTokensPerClause + 9.
```

For the empty input-only regression problem this coordinate is exactly
`287`. `finalTape_represents` preserves the raw input, while
`finalOutside_contains_finalTokenSlot` audits the unary coordinate retained
in the workspace.

## External compiled bound

The exact new work is one outer launch, one selected appender, one inner
launch, and one cursor scan. The external raw-transition polynomial evaluates
to

```text
BuilderFourthClauseSecondLiteralPrefix.rawTimeBound(n)
+ 618
+ 24*n
+ 12*FormulaWidth
+ 12*BuilderFourthClauseSeparatorStep.cursorWord.length.
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
suffix and 4276-rule global base, both bridges, exact final tape and bits,
`Finish`, first padding, polynomial evaluation, compiled acceptance, and all
fail-closed boundaries.

```sh
lake env lean -DwarningAsError=true \
  lean-audit/PNPConcreteCookLevinBuilderFourthClausePrefixAxiomAudit.lean
lake env lean -DwarningAsError=true \
  lean-regression/PNPConcreteCookLevinBuilderFourthClausePrefix.lean
node --test \
  audits/lean-concrete-cook-levin-builder-fourth-clause-prefix0.test.mjs
```

The combined kernel audit covers all 55 public declarations plus the two
reviewed cursor dead-loop facts. Fourteen declarations have empty closure, ten
use only `propext`, and 33 use only `propext` and `Quot.sound`. No
declaration reaches a project axiom, `Classical.choice`, `sorry`, `admit`,
SAT/minimization code, host-side composition, or a caller-supplied execution
certificate.

## Generated publication artifacts

The compiled environment records inventory coordinate
`PNP-LEAN-THEOREM-INVENTORY-2026-07-21-66`, 9,758 declarations, 5,253
theorems, 3,229 assumption-free theorems, 86 source-closure modules, and 1,334
reviewed milestone candidates. Its canonical byte SHA-256 is
`a273572123347ada7b362371a3f30fe17c8c0ac359e3d440d6fd4583eaffeedf`;
the Lean source-closure SHA-256 is
`98a5d9fc7a5821a2d39b2b55be7fb99f5b2a23485f7464b6a404051a3046a423`.

Publication map coordinate `PNP-FORMAL-PUBLICATION-MAP-2026-07-21-66` has
46 milestones and 1,334 exact kernel-type fingerprints. Its exact file
SHA-256 is
`1cbf9f3e53e0c57599123f60ef7049ffe8b0c45e96529ea8b7acacd4fa225172`,
and its canonical reviewed-object fingerprint is
`dbfe0ebce50bf597ee3a884a2816446ef0afa0161918491f6cfce7e022e3c18f`.

Status coordinate `PNP-FORMAL-RECONSTRUCTION-STATUS-2026-07-21-66` has
SHA-256 `66385722de2685d469eba26619080dc8659e3c87dcdaf5e677da7cf08ff9943a`.
The generated report coordinate is
`PNP-CANONICAL-FORMAL-RECONSTRUCTION-REPORT-2026-07-21-66`; its 96,022-byte
TeX SHA-256 is `d4dd8e112e1153bb7579f10afe461e95a498285158fd141f470ab52dae10c993`
and its 42-page, 351,128-byte PDF SHA-256 is
`ba99e0d0bda29e0a228f88cc74f1658a31992cf62b1d7e08ed9a1c1e0a222ab8`.
All activation fingerprints remain unset and the publication gate remains
false.

## Remaining boundary

This milestone completes only clause four. It advances once to the first
padding coordinate but does not traverse clause-four padding, implement an
arbitrary dynamic formula cursor, emit the remaining
formula body, construct a complete raw formula builder, provide builder
`RawRefinement` or a `PolynomialReduction`, prove CNF-SAT NP-complete or in
P, or establish `PNP.Main.p_eq_np`. The four project assumptions, six
blockers, unset activation fingerprints, and false publication gate remain
unchanged.
