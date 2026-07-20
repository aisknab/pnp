# Concrete Cook–Levin fourth-clause separator step

`lean/PNP/Concrete/CookLevinBuilderFourthClauseSeparatorStep.lean` composes
the complete raw-input-through-third-clause-padding machine with the already
audited selected `Sep` appender and fixed cursor-advance table. Every raw input
therefore emits the separator beginning clause four and advances the retained
unary coordinate to that clause's first literal sign.

The exact finite output is

```text
T^FormulaWidth F
Sep T F T T F T T T F Finish
Sep F F F T F Finish
Sep F F F T T F Finish
Sep.
```

Rectangular `none` padding is skipped by the canonical schedule emitter. The
following direct token opportunity is constructively proved to be `F`, the
negative sign of the first excluded-pair literal in clause four. That token is
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
`BuilderThirdClausePaddingRun.machine` behind one more total nine-symbol
bridge. The complete symbolic rule count is

```text
3300
+ width-evaluator ruleCount
+ body-start-coordinate evaluator ruleCount
+ first-literal-coordinate evaluator ruleCount
+ first-clause-coordinate evaluator ruleCount
+ first-clause-padding evaluator ruleCount
+ second-clause-target evaluator ruleCount
+ second-clause-padding evaluator ruleCount
+ third-clause-target evaluator ruleCount
+ third-clause-padding evaluator ruleCount
+ fourth-clause-target evaluator ruleCount.
```

The constant is the predecessor's `3178`, the outer nine-rule bridge, and the
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

The independent schedule proof unfolds the first four clauses of the first
shape constraint. It identifies the first positive at-least-one clause on
variables zero, one, and two, then three excluded-pair clauses, while accounting
for all three rectangular padding regions. Consequently:

- `fourthClauseStartTokens_eq_canonical_formula_prefix` proves that the finite
  output is a prefix of `encodeCNFTokens problem.formula`;
- `finalTokenBits_eq_encodedFormula_fourthClauseStart` proves exact equality
  with `encodedFormula.take (2 * (FormulaWidth + 28))`;
- `nextTokenSlot_direct_eq_f` proves the retained coordinate contains `F`;
- `specification_separator_step` and `specification_next_step` agree with the
  token-level specification cursor before and after the executed transition.

The final coordinate is

```text
formulaVariableSlotBound + 1 + 3 * formulaTokensPerClause + 1,
```

and `finalOutside_contains_finalTokenSlot` proves that coordinate is retained
as a unary root in the preserved workspace.

## External compiled bound

The exact work count is the predecessor count, one outer launch, the selected
appender, one reused inner launch, and the complete cursor scan. The external
raw-transition polynomial evaluates to

```text
BuilderThirdClausePaddingRun.rawTimeBound(n)
+ 426
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
  lean-audit/PNPConcreteCookLevinBuilderFourthClauseSeparatorStepAxiomAudit.lean
lake env lean -DwarningAsError=true \
  lean-regression/PNPConcreteCookLevinBuilderFourthClauseSeparatorStep.lean
node --test \
  audits/lean-concrete-cook-levin-builder-fourth-clause-separator-step0.test.mjs
```

The combined audit covers all 48 public declarations in the new module plus
eight reviewed interfaces reused from the separator/cursor suffix and its
dead-state boundary. Exactly 14 closures are empty, 11 use only `propext`, and
31 use only `propext` and `Quot.sound`. No declaration reaches a project axiom,
`Classical.choice`, `sorry`, `admit`, SAT/minimization code, host-side
composition, or a caller-supplied execution certificate.

## Generated publication artifacts

The compiled environment records inventory coordinate
`PNP-LEAN-THEOREM-INVENTORY-2026-07-20-63`, 9,336 declarations, 4,934
theorems, 3,152 assumption-free theorems, 3,264 excluded private declarations,
83 source-closure modules, and 1,160 reviewed milestone candidates. Its
5,841,311 canonical bytes have SHA-256
`afffa1ba06055ce4b3d8a43b015fa4afa7e2477436279f84b587dd8a362e4c1a`;
the Lean source-closure SHA-256 is
`c8e724e433996168ad1c937d9c8b68af8dc034d425577302c6d58b2334c8d66c`.

Publication map coordinate `PNP-FORMAL-PUBLICATION-MAP-2026-07-20-63` has
43 milestones, of which 40 are earned and the same three global milestones are
unearned, plus 1,160 exact kernel-type fingerprints. Its 348,488 canonical
file bytes have SHA-256
`d6fea680626e9cd4d61efb617945cea9a7df639291627a39e0e2fe92fdc2bcdb`;
its canonical reviewed-object fingerprint is
`a02ecb01312466a1ed23dd841cc5057cdf0af82dce6ae67b63c8c6a4e80cf555`.

Status coordinate `PNP-FORMAL-RECONSTRUCTION-STATUS-2026-07-20-63` has
867,595 bytes and SHA-256
`b8d52a3d04a9208b8d77dda097bcbf7d41e00917ff59ed8c3089717108967483`.
The generated report coordinate is
`PNP-CANONICAL-FORMAL-RECONSTRUCTION-REPORT-2026-07-20-63`; its 87,108-byte
TeX has SHA-256
`d215fbafd0c32416e8afd0f7f78e865461c49fd8a8406678841c51f588cbe0d7`,
and its 39-page, 342,201-byte PDF has SHA-256
`1d9460a995b1afefa98ac519558ca458f7e40cdd8fe20c0b6a70323367199f2d`.
All activation fingerprints remain unset and the publication gate remains
false.

## Remaining boundary

This is one fixed populated token transition and one unary cursor advance. It
does not emit the following `F`, complete clause four, interpret arbitrary
schedule coordinates, implement a general dynamic formula cursor, emit the
remaining formula body, construct a complete raw formula builder, provide
builder `RawRefinement` or a `PolynomialReduction`, prove CNF-SAT NP-complete
or in P, or establish `PNP.Main.p_eq_np`. The four project assumptions, six
blockers, unset activation fingerprints, and false publication gate remain
unchanged.
