# Concrete Cook–Levin second-clause separator step

`lean/PNP/Concrete/CookLevinBuilderSecondClauseSeparatorStep.lean` composes
the complete raw-input-through-first-clause-padding machine with one selected
`Sep` token appender and the existing fixed cursor-advance table. Every raw
input therefore emits the separator beginning clause two and advances the
retained unary coordinate to that clause's first literal sign.

The exact emitted token list is

```text
T^FormulaWidth F Sep T F T T F T T T F Finish Sep.
```

This is the canonical prefix through the first token of clause two. The
following direct token opportunity is constructively proved to be `F`, the
negative sign of the first excluded-pair literal. That next token is observed
by the specification theorem but is not emitted by this milestone.

## Literal composition

`SeparatorCursor.appender` reuses the complete 59-rule token-appender table
with its start state fixed to the `Sep` request. A total nine-symbol bridge
then launches `BuilderDynamicTokenCursorStep.CursorAdvance.machine`, the
existing 45-rule cursor table. Their collision-free `WorkChain` has exactly

```text
59 + 9 + 45 = 113 rules.
```

The outer `WorkChain` places that suffix after
`BuilderFirstClausePaddingRun.machine` behind one more total nine-symbol
bridge. The complete symbolic rule count is

```text
1366
+ width-evaluator ruleCount
+ body-start-coordinate evaluator ruleCount
+ first-literal-coordinate evaluator ruleCount
+ first-clause-coordinate evaluator ruleCount
+ remaining-padding evaluator ruleCount
+ second-clause-target evaluator ruleCount.
```

The constant is the predecessor's `1244`, the outer nine-rule bridge, and the
113-rule suffix. Only the final cursor component supplies global accept and
reject states. Both local and global rule lists are pairwise query-distinct,
so first-match dispatch cannot be shadowed across either bridge.

## Exact trace and canonical output

`prefix_workRunExact` transports the complete predecessor trace into the
outer first-state image. `prefixSeparator_launch_workStep` proves the first
bridge literally preserves every work symbol. `appender_workRunExact` appends
the requested separator while preserving the raw input, unary workspace, and
exterior garbage. `separatorCursor_launch_workStep` proves the second bridge,
and `cursor_workRunExact` performs the complete bidirectional unary scan.
`workRunExact` composes those pieces into one exact all-input execution.

The independent schedule proof unfolds the first two clauses of the first
shape constraint. It identifies the first rectangle as the positive
at-least-one clause on variables zero, one, and two, removes all rectangular
padding, and identifies the next clause as an excluded pair. Consequently:

- `secondClauseStartTokens_eq_canonical_formula_prefix` proves that the finite
  output is a prefix of `encodeCNFTokens problem.formula`;
- `finalTokenBits_eq_encodedFormula_secondClauseStart` proves exact equality
  with `encodedFormula.take (2 * (FormulaWidth + 13))`;
- `nextTokenSlot_direct_eq_f` proves the retained coordinate contains `F`;
- `specification_separator_step` and `specification_next_step` agree with the
  token-level specification cursor before and after the executed transition.

The final coordinate is

```text
formulaVariableSlotBound + 1 + formulaTokensPerClause + 1,
```

and `finalOutside_contains_finalTokenSlot` proves that coordinate is retained
as a unary root in the preserved workspace.

## External compiled bound

The exact work count is the predecessor count, one outer launch, the selected
appender, one inner launch, and the complete cursor scan. The external
raw-transition polynomial evaluates to

```text
BuilderFirstClausePaddingRun.rawTimeBound(n)
+ 246
+ 24*n
+ 12*FormulaWidth
+ 12*cursorWord.length.
```

The constant covers both six-transition compiled bridges, the appender's
fixed overhead, and the cursor's fixed overhead. `rawTimeBound_le` proves the
polynomial bounds six times the exact work trace. The compiled interfaces then
prove exact execution, polynomial-fuel execution, ordinary-start
blank-equivalence, acceptance, and non-timeout.

## Fail-closed boundaries and audits

The predecessor endpoint remains timeout before the outer bridge, and the
successful appender endpoint remains timeout before the cursor bridge. A
malformed appender tally symbol, malformed appender output symbol, or malformed
cursor scratch symbol cannot reach either global halt. The cursor case enters
an explicit nonhalting dead self-loop. One-step-short total fuel also remains
timeout.

The regression covers empty input, one-bit zero and one, odd and even lengths,
all-zero and all-one words, input-only and paired verifiers, exact rule/step/
coordinate values, both bridges, exact final token bits and tape geometry,
the direct `Sep` and following `F` outcomes, compiled acceptance, polynomial
evaluation, and every fail-closed boundary.

```sh
lake env lean -DwarningAsError=true \
  lean-audit/PNPConcreteCookLevinBuilderSecondClauseSeparatorStepAxiomAudit.lean
lake env lean -DwarningAsError=true \
  lean-regression/PNPConcreteCookLevinBuilderSecondClauseSeparatorStep.lean
node --test \
  audits/lean-concrete-cook-levin-builder-second-clause-separator-step0.test.mjs
```

The combined audit covers all 54 public declarations in the new module plus
the two reviewed cursor-dispatch facts required from its predecessor. Every
closure is restricted to the approved Lean-standard allowlist. No declaration
reaches a project axiom, `Classical.choice`, `sorry`, `admit`, SAT/minimization
code, host-side composition, or a caller-supplied execution certificate.

## Generated publication artifacts

The compiled environment records inventory coordinate
`PNP-LEAN-THEOREM-INVENTORY-2026-07-18-53`, 8,094 declarations, 3,974
theorems, 2,939 assumption-free theorems, 73 source-closure modules, and 673
reviewed milestone candidates. Its canonical byte SHA-256 is
`23d0d6f56d811dd59a52d9e89a937672954a01629eb99e1f762a4efe89c6efd2`;
the Lean source-closure SHA-256 is
`e2c175e1ff0f499530a84338ef1f93404d4d0749b79df1e10719f053691ca91a`.

Publication map coordinate `PNP-FORMAL-PUBLICATION-MAP-2026-07-18-53` has
33 milestones. Its exact file SHA-256 is
`57f9fa53f4cdaf9e9dd13f6e135c35f17cc4d9e3d44645692553a01f7f883116`,
and its canonical reviewed-object fingerprint is
`406f7d72303e1c4f79778fba5098ae2c9164c54ddf2372974d6ba9601c87f0d4`.
All activation fingerprints remain unset and the publication gate remains
false.

Status coordinate `PNP-FORMAL-RECONSTRUCTION-STATUS-2026-07-18-53` has
SHA-256 `bbe730c93779ff35add0400446acb94627794be76604ca9f747dc19584b16bbb`.
The generated canonical report coordinate is
`PNP-CANONICAL-FORMAL-RECONSTRUCTION-REPORT-2026-07-18-53`; its TeX SHA-256
is `47d21ad3f4c4f1cd4d3e366ba212419b53e0cbecb78c9c8ffe3900cc37f32b56`
and its 27-page, 314,641-byte PDF SHA-256 is
`8b922c3528384db21e8ea0c9986a18af98d182d803a445b9cd0bbfaa7c4338d1`.

## Remaining boundary

This is one fixed populated token transition and one unary cursor advance. It
does not emit the following `F`, complete clause two, interpret arbitrary
schedule coordinates, implement a general dynamic formula cursor, emit the
remaining formula body, construct a complete raw formula builder, provide
builder `RawRefinement` or a `PolynomialReduction`, prove CNF-SAT NP-complete
or in P, or establish `PNP.Main.p_eq_np`. The four project assumptions, six
blockers, unset activation fingerprints, and false publication gate remain
unchanged.
