# Concrete Cook–Levin second-constraint separator step

`lean/PNP/Concrete/CookLevinBuilderSecondConstraintSeparatorStep.lean` composes
the complete first-constraint padding run with the already audited selected
`Sep` appender and fixed unary cursor-advance table. Every raw input emits
exactly the separator beginning the second scheduled constraint and advances
the retained unary coordinate to that constraint's first literal sign.

The finite token output is the complete four populated clauses of the first
constraint followed by one new `Sep`. Rectangular `none` padding is skipped by
the canonical schedule emitter. The following direct token opportunity is
constructively proved to be `T`, the positive sign that begins the next
constraint's at-least-one clause. That token is observed but is not emitted by
this milestone.

## Literal composition

The suffix is reused unchanged from
`BuilderSecondClauseSeparatorStep.SeparatorCursor.machine`. It consists of the
selected 59-rule token appender, a total nine-symbol bridge, and the 45-rule
cursor table:

```text
59 + 9 + 45 = 113 rules.
```

One outer `WorkChain` places that suffix after
`BuilderFirstConstraintPaddingRun.machine` behind another total nine-symbol
bridge. The complete symbolic rule count is `4554` plus the sixteen inherited
and generated unary-evaluator rule counts. Only the final cursor component
supplies the global accept and reject states. The reused state embeddings are
injective, their images are disjoint, and the combined rule list is pairwise
query-distinct, so neither bridge can be shadowed.

## Exact trace and canonical output

`prefix_workRunExact` transports the full predecessor trace into the outer
first-state image. `prefixSeparator_launch_workStep` proves the outer bridge.
`appender_workRunExact` appends the selected separator while preserving the raw
input, unary workspace, and exterior garbage. `separatorCursor_launch_workStep`
proves the inner bridge, and `cursor_workRunExact` performs the complete
bidirectional unary scan. `suffix_workRunExact` and `workRunExact` compose those
pieces into exact all-input executions.

The constructive schedule proof unfolds the complete first scheduled
constraint and proves that the next scheduled constraint begins with a
nonempty exactly-one constraint. Consequently:

- `secondConstraintStartTokens_eq_canonical_formula_prefix` proves the finite
  output is a prefix of `encodeCNFTokens problem.formula`;
- `finalTokenBits_eq_encodedFormula_secondConstraintStart` proves exact equality
  with `encodedFormula.take (2 * (FormulaWidth + 37))`;
- `nextTokenSlot_direct_eq_t` proves the retained coordinate contains `T`;
- `specification_separator_step` and `specification_next_step` agree with the
  token-level cursor before and after the transition.

Writing `V = formulaVariableSlotBound`, `C = formulaTokensPerClause`, and
`Q = formulaClauseSlotsPerConstraint`, the final coordinate is

```text
V + 1 + Q * C + 1.
```

`finalOutside_contains_finalTokenSlot` proves that coordinate is retained as a
unary root in the preserved workspace.

## External compiled bound

The exact work count is the predecessor count, one outer launch, the selected
appender, one reused inner launch, and the complete cursor scan. The external
raw-transition polynomial evaluates to

```text
BuilderFirstConstraintPaddingRun.rawTimeBound(n)
+ 534
+ 24*n
+ 12*FormulaWidth
+ 12*cursorWord.length.
```

`rawTimeBound_le` proves that polynomial bounds six times the exact work trace.
The compiled interfaces prove exact execution, polynomial-fuel execution,
ordinary-start blank equivalence, acceptance, and non-timeout.

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
emitted `Sep`, retained `T`, compiled acceptance, polynomial evaluation, and
every fail-closed boundary.

```sh
lake env lean -DwarningAsError=true \
  lean-audit/PNPConcreteCookLevinBuilderSecondConstraintSeparatorStepAxiomAudit.lean
lake env lean -DwarningAsError=true \
  lean-regression/PNPConcreteCookLevinBuilderSecondConstraintSeparatorStep.lean
node --test \
  audits/lean-concrete-cook-levin-builder-second-constraint-separator-step0.test.mjs
```

The combined audit covers all 48 public declarations in the new module plus
eight reviewed interfaces reused from the separator/cursor suffix and its
dead-state boundary. Exactly 14 closures are empty, 11 use only `propext`, and
31 use only `propext` and `Quot.sound`. No declaration reaches a project axiom,
`Classical.choice`, `sorry`, `admit`, native/SAT shortcuts, host-side schedule
lookup, or a caller-supplied execution certificate.

## Generated publication artifacts

The compiled environment records inventory coordinate
`PNP-LEAN-THEOREM-INVENTORY-2026-07-22-70`: 10,300 declarations, 5,678
theorems, 3,306 assumption-free theorems, 3,828 excluded private declarations,
90 source-closure modules, and 1,479 reviewed milestone candidates. Its
7,553,204 canonical bytes have SHA-256
`f3e8f9024eeaf12bc26854355b378fc14d0d9e777cab545539573f48b476ff0b`;
the Lean source-closure SHA-256 is
`f8b784bc6158939b63a2ae7e1a0c4d03a5603778585575d424971e1c70c95442`.

Publication map coordinate `PNP-FORMAL-PUBLICATION-MAP-2026-07-22-70` has 50
milestones, of which 47 are earned and the same three global milestones remain
unearned, plus 1,479 exact kernel-type fingerprints. Its canonical reviewed-
object fingerprint is
`f791433da2ab37e85f6f25d960eab10d0b21b3d20d546047fac5d7f59f58520e`.
Its 452,513 canonical file bytes have SHA-256
`0949803e659d81dfaffdc9aca08d2c0ac57f6828d23e3b47f629a1f11c7eff76`.

Status coordinate `PNP-FORMAL-RECONSTRUCTION-STATUS-2026-07-22-70` has
1,131,717 bytes and SHA-256
`a30ee68df44c5d1b02f243388d43ef20f310ee608c18d5c84c9c4fb4daf41f8e`.
The generated report coordinate is
`PNP-CANONICAL-FORMAL-RECONSTRUCTION-REPORT-2026-07-22-70`; its 104,505-byte
TeX has SHA-256
`f144109d089e6b0fab74519f5e6ee31fb611ea31b5a880b46efa43bbfa3d26bf`,
and its 46-page, 359,937-byte PDF has SHA-256
`504d4a9a4c8befd068d1ea94379f4c428d5e003bde5367fc905d5d69dbf5c5af`.

All activation fingerprints remain unset, all four project assumptions and six
blockers remain, `PNP.Main.p_eq_np` remains absent, and the concrete publication
gate remains false.

## Remaining boundary

This is one fixed populated token transition and one unary cursor advance. It
does not emit the following `T`, emit the second constraint's first literal,
traverse the second constraint, interpret arbitrary schedule coordinates,
implement a general dynamic formula cursor, emit the remaining formula body,
construct a complete raw formula builder, provide builder `RawRefinement` or a
`PolynomialReduction`, prove CNF-SAT NP-complete or in P, or establish
`PNP.Main.p_eq_np`.
