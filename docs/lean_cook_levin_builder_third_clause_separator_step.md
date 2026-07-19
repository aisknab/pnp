# Concrete Cook–Levin third-clause separator step

`lean/PNP/Concrete/CookLevinBuilderThirdClauseSeparatorStep.lean` composes
the complete raw-input-through-second-clause-padding machine with the already
audited selected `Sep` appender and fixed cursor-advance table. Every raw input
therefore emits the separator beginning clause three and advances the retained
unary coordinate to that clause's first literal sign.

The exact finite output is

```text
T^FormulaWidth F
Sep T F T T F T T T F Finish
Sep F F F T F Finish
Sep.
```

Rectangular `none` padding is skipped by the canonical schedule emitter. The
following direct token opportunity is constructively proved to be `F`, the
negative sign of the first excluded-pair literal in clause three. That token is
observed by the specification theorem but is not emitted by this milestone.

## Literal composition

The suffix is reused unchanged from
`BuilderSecondClauseSeparatorStep.SeparatorCursor.machine`. It consists of the
complete 59-rule token appender selected for `Sep`, a total nine-symbol bridge,
and the 45-rule cursor table:

```text
59 + 9 + 45 = 113 rules.
```

The outer `WorkChain` places that suffix after
`BuilderSecondClausePaddingRun.machine` behind one more total nine-symbol
bridge. The complete symbolic rule count is

```text
2272
+ width-evaluator ruleCount
+ body-start-coordinate evaluator ruleCount
+ first-literal-coordinate evaluator ruleCount
+ first-clause-coordinate evaluator ruleCount
+ first-clause-padding evaluator ruleCount
+ second-clause-target evaluator ruleCount
+ second-clause-padding evaluator ruleCount
+ third-clause-target evaluator ruleCount.
```

The constant is the predecessor's `2150`, the outer nine-rule bridge, and the
reused 113-rule suffix. Only the final cursor component supplies global accept
and reject states. The reused state embeddings are injective, their images are
disjoint, and the combined rule list is pairwise query-distinct, so first-match
dispatch cannot be shadowed across either bridge.

## Exact trace and canonical output

`prefix_workRunExact` transports the complete predecessor trace into the outer
first-state image. `prefixSeparator_launch_workStep` proves the outer bridge
preserves every work symbol. `appender_workRunExact` appends the selected
separator while preserving the raw input, unary workspace, and exterior
garbage. `separatorCursor_launch_workStep` proves the reused inner bridge, and
`cursor_workRunExact` performs the complete bidirectional unary scan.
`workRunExact` composes those pieces into one exact all-input execution.

The independent schedule proof unfolds the first three clauses of the first
shape constraint. It identifies the first positive at-least-one clause on
variables zero, one, and two, then two excluded-pair clauses, while accounting
for both rectangular padding regions. Consequently:

- `thirdClauseStartTokens_eq_canonical_formula_prefix` proves that the finite
  output is a prefix of `encodeCNFTokens problem.formula`;
- `finalTokenBits_eq_encodedFormula_thirdClauseStart` proves exact equality
  with `encodedFormula.take (2 * (FormulaWidth + 20))`;
- `nextTokenSlot_direct_eq_f` proves the retained coordinate contains `F`;
- `specification_separator_step` and `specification_next_step` agree with the
  token-level specification cursor before and after the executed transition.

The final coordinate is

```text
formulaVariableSlotBound + 1 + 2 * formulaTokensPerClause + 1,
```

and `finalOutside_contains_finalTokenSlot` proves that coordinate is retained
as a unary root in the preserved workspace.

## External compiled bound

The exact work count is the predecessor count, one outer launch, the selected
appender, one reused inner launch, and the complete cursor scan. The external
raw-transition polynomial evaluates to

```text
BuilderSecondClausePaddingRun.rawTimeBound(n)
+ 330
+ 24*n
+ 12*FormulaWidth
+ 12*cursorWord.length.
```

`rawTimeBound_le` proves the polynomial bounds six times the exact work trace.
The compiled interfaces then prove exact execution, polynomial-fuel execution,
ordinary-start blank-equivalence, acceptance, and non-timeout.

## Fail-closed boundaries and audits

The predecessor endpoint remains timeout before the outer bridge, and the
successful appender endpoint remains timeout before the cursor bridge. A
malformed appender tally symbol, malformed appender output symbol, or malformed
cursor scratch symbol cannot reach either global halt. The cursor case enters
an explicit nonhalting dead self-loop. One-step-short total fuel also remains
timeout.

The regression covers empty input, one-bit zero and one, odd and even lengths,
all-zero and all-one words, input-only and paired verifiers, exact rule/step/
coordinate values, both bridges, exact final token bits and tape geometry, the
direct `Sep` and following `F` outcomes, compiled acceptance, polynomial
evaluation, and every fail-closed boundary.

```sh
lake env lean -DwarningAsError=true \
  lean-audit/PNPConcreteCookLevinBuilderThirdClauseSeparatorStepAxiomAudit.lean
lake env lean -DwarningAsError=true \
  lean-regression/PNPConcreteCookLevinBuilderThirdClauseSeparatorStep.lean
node --test \
  audits/lean-concrete-cook-levin-builder-third-clause-separator-step0.test.mjs
```

The combined audit covers all 48 public declarations in the new module plus
eight reviewed interfaces reused from the separator/cursor suffix and its
dead-state boundary. Exactly 14 closures are empty, 11 use only `propext`, and
31 use only `propext` and `Quot.sound`. No declaration reaches a project axiom,
`Classical.choice`, `sorry`, `admit`, SAT/minimization code, host-side
composition, or a caller-supplied execution certificate.

## Generated publication artifacts

The compiled environment records inventory coordinate
`PNP-LEAN-THEOREM-INVENTORY-2026-07-19-58`, 8,680 declarations, 4,425
theorems, 3,043 assumption-free theorems, 78 source-closure modules, and 912
reviewed milestone candidates. Its canonical byte SHA-256 is
`9db4fc68c45e470777c5607c0ea1440e86c59b1222d7e2d62f2898b3d424c8e7`;
the Lean source-closure SHA-256 is
`c34dec0242ed84b5f915166a55ee1183dd0450cee9445b8dd0a8721c765facaf`.

Publication map coordinate `PNP-FORMAL-PUBLICATION-MAP-2026-07-19-58` has
38 milestones. Its exact file SHA-256 is
`daddcdf827fd1b1643995ddbd8b2e449a1608a2e6f73444f3b945a78b5ad6f40`,
and its canonical reviewed-object fingerprint is
`6790039daf44d45b6cae9351964e4ac1a2de635b76a71504afcc387630123747`.
All activation fingerprints remain unset and the publication gate remains
false.

Status coordinate `PNP-FORMAL-RECONSTRUCTION-STATUS-2026-07-19-58` has
SHA-256 `146bbf914afe66256f6573dcc59a8cdfe825420f7cb021829f55708ab64a48ad`.
The generated canonical report coordinate is
`PNP-CANONICAL-FORMAL-RECONSTRUCTION-REPORT-2026-07-19-58`; its 71,742-byte
TeX SHA-256 is
`d15fab89c2bf172de01f4bb69ec6a804450d755d1a6a9b274df1dafd8ec5cc16`
and its 33-page, 328,449-byte PDF SHA-256 is
`24d577e14345f5e4aee7c2d84a560a3eb3bb652a6d9e50feb15bc0adaa182a43`.

## Remaining boundary

This is one fixed populated token transition and one unary cursor advance. It
does not emit the following `F`, complete clause three, interpret arbitrary
schedule coordinates, implement a general dynamic formula cursor, emit the
remaining formula body, construct a complete raw formula builder, provide
builder `RawRefinement` or a `PolynomialReduction`, prove CNF-SAT NP-complete
or in P, or establish `PNP.Main.p_eq_np`. The four project assumptions, six
blockers, unset activation fingerprints, and false publication gate remain
unchanged.
