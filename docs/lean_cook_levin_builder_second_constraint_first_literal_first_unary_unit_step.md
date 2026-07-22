# Concrete Cook–Levin second-constraint first-literal first unary-unit step

`lean/PNP/Concrete/CookLevinBuilderSecondConstraintFirstLiteralFirstUnaryUnitStep.lean`
composes the complete second-constraint first-literal sign step with the already audited
selected `T` appender and fixed unary cursor-advance table. Every raw input
emits exactly the first unary unit of the second constraint's first variable
index and advances the retained unary coordinate to that index's second unit.

The finite output is the complete four populated clauses of the first
constraint followed by the next constraint's `Sep`, positive-sign `T`, and one
new unary `T`. Rectangular
`none` padding is skipped by the canonical schedule emitter. The following
direct token opportunity is constructively proved to be another `T`: the second
unary unit of an index that is at least three. That second unary token is
observed but is not emitted by this milestone.

## Literal composition

The suffix is reused unchanged from
`BuilderSecondClauseSecondLiteralPrefix.TrueTokenCursor.machine`. It consists
of the selected 59-rule true-token appender, a total nine-symbol bridge, and the
45-rule cursor table:

```text
59 + 9 + 45 = 113 rules.
```

One outer `WorkChain` places that suffix after
`BuilderSecondConstraintFirstLiteralSignStep.machine` behind another total
nine-symbol bridge. The complete symbolic rule count is `4798` plus the sixteen
inherited and generated unary-evaluator rule counts. Only the final cursor
component supplies the global accept and reject states. The reused state
embeddings are injective, their images are disjoint, and the combined rule list
is pairwise query-distinct, so neither bridge can be shadowed.

## Exact trace and canonical output

`prefix_workRunExact` transports the full predecessor trace into the outer
first-state image. `prefixFirstUnaryUnit_launch_workStep` proves the outer bridge.
`appender_workRunExact` appends the selected first unary unit while preserving the
raw input, unary workspace, and exterior garbage.
`trueTokenCursor_launch_workStep` proves the inner bridge, and
`cursor_workRunExact` performs the complete bidirectional unary scan.
`suffix_workRunExact` and `workRunExact` compose those pieces into exact
all-input executions.

The constructive schedule proof handles both possible shapes of the second
scheduled constraint. When the tape rectangle has width one, its first literal
is the first head variable, whose index follows the nonempty symbol block. At
larger widths it is the blank-symbol variable at the next tape position. In
both cases the variable index is at least three, so its unary encoding starts
with three `T` tokens. Consequently:

- `secondConstraintFirstLiteralFirstUnaryTokens_eq_canonical_formula_prefix` proves
  the finite output is a prefix of `encodeCNFTokens problem.formula`;
- `finalTokenBits_eq_encodedFormula_secondConstraintFirstLiteralFirstUnary` proves
  exact equality with `encodedFormula.take (2 * (FormulaWidth + 39))`;
- `nextTokenSlot_direct_eq_t` proves the retained coordinate contains the
  second unary `T`;
- `specification_firstUnaryUnit_step` and `specification_next_step` agree with the
  token-level cursor before and after the transition.

Writing `V = formulaVariableSlotBound`, `C = formulaTokensPerClause`, and
`Q = formulaClauseSlotsPerConstraint`, the final coordinate is

```text
V + 1 + Q * C + 3.
```

`finalOutside_contains_finalTokenSlot` proves that coordinate is retained as a
unary root in the preserved workspace.

## External compiled bound

The exact work count is the predecessor count, one outer launch, the selected
appender, one reused inner launch, and the complete cursor scan. The external
raw-transition polynomial evaluates to

```text
BuilderSecondConstraintFirstLiteralSignStep.rawTimeBound(n)
+ 558
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
emitted first unary `T`, retained second unary `T`, compiled acceptance, polynomial
evaluation, and every fail-closed boundary.

```sh
lake env lean -DwarningAsError=true \
  lean-audit/PNPConcreteCookLevinBuilderSecondConstraintFirstLiteralFirstUnaryUnitStepAxiomAudit.lean
lake env lean -DwarningAsError=true \
  lean-regression/PNPConcreteCookLevinBuilderSecondConstraintFirstLiteralFirstUnaryUnitStep.lean
node --test \
  audits/lean-concrete-cook-levin-builder-second-constraint-first-literal-first-unary-unit-step0.test.mjs
```

The combined audit covers all 48 public declarations in the new module plus
eight reviewed interfaces reused from the true-token/cursor suffix and its
dead-state boundary. Exactly 14 closures are empty, 11 use only `propext`, and
31 use only `propext` and `Quot.sound`. No declaration reaches a project axiom,
`Classical.choice`, `sorry`, `admit`, native/SAT shortcuts, host-side schedule
lookup, or a caller-supplied execution certificate.

## Generated publication artifacts

The compiled environment records inventory coordinate
`PNP-LEAN-THEOREM-INVENTORY-2026-07-23-72`: 10,493 declarations, 5,841
theorems, 3,333 assumption-free theorems, 3,971 excluded private declarations,
92 source-closure modules, and 1,547 reviewed milestone candidates. Its
7,937,144 canonical bytes have SHA-256
`02229cdf19b7d630a68733a80a4bad00f7d9c7ae3bfd64f42095e5b2c5e4f474`;
the Lean source-closure SHA-256 is
`dfd54b5c1fb44d65cb5444a9e4f9b105242a58148c7afda8c2db946485c693d7`.

Publication map coordinate `PNP-FORMAL-PUBLICATION-MAP-2026-07-23-72` has 52
milestones, of which 49 are earned and the same three global milestones remain
unearned, plus 1,547 exact kernel-type fingerprints. Its canonical reviewed-
object fingerprint is
`44e06879a3b0201e31ef03c2564797273dacbd9028397961e07e8e1580c86ed9`.
Its 478,150 canonical file bytes have SHA-256
`d16f975fb526eda5028c34c526889dbcda517dc8a806d9ec7a64f016d651d13f`.

Status coordinate `PNP-FORMAL-RECONSTRUCTION-STATUS-2026-07-23-72` has
1,194,750 bytes and SHA-256
`c068019b669e621581e2a1da0c38e51940976af6b286031a5cb356124f9baa1a`.
The generated report coordinate is
`PNP-CANONICAL-FORMAL-RECONSTRUCTION-REPORT-2026-07-23-72`; its 112,300-byte
TeX has SHA-256
`3b02be283020585655fb3d296caec0e48438e0f805e1378b3bfefef3547d3563`,
and its 49-page, 364,806-byte PDF has SHA-256
`c693013d81416b9388008b30759028bd853b0e9103db2093b0154d9ebf4d151c`.

All activation fingerprints remain unset, all four project assumptions and six
blockers remain, `PNP.Main.p_eq_np` remains absent, and the concrete publication
gate remains false.

## Remaining boundary

This is one fixed populated token transition and one unary cursor advance. It
does not emit the following second unary `T`, complete the second constraint's first
literal, traverse the second constraint, interpret arbitrary schedule
coordinates, implement a general dynamic formula cursor, emit the remaining
formula body, construct a complete raw formula builder, provide builder
`RawRefinement` or a `PolynomialReduction`, prove CNF-SAT NP-complete or in P,
or establish `PNP.Main.p_eq_np`.
