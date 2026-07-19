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
dead-state boundary. Every closure is restricted to the approved Lean-standard
allowlist. No declaration reaches a project axiom, `Classical.choice`, `sorry`,
`admit`, SAT/minimization code, host-side composition, or a caller-supplied
execution certificate.

## Generated publication artifacts

The theorem inventory, publication map, reconstruction status, canonical TeX,
PDF, and report metadata are regenerated mechanically after the kernel audit.
Their resulting coordinates, byte counts, page count, and SHA-256 identities
are recorded here as part of the reviewed publication diff.

## Remaining boundary

This is one fixed populated token transition and one unary cursor advance. It
does not emit the following `F`, complete clause three, interpret arbitrary
schedule coordinates, implement a general dynamic formula cursor, emit the
remaining formula body, construct a complete raw formula builder, provide
builder `RawRefinement` or a `PolynomialReduction`, prove CNF-SAT NP-complete
or in P, or establish `PNP.Main.p_eq_np`. The four project assumptions, six
blockers, unset activation fingerprints, and false publication gate remain
unchanged.
