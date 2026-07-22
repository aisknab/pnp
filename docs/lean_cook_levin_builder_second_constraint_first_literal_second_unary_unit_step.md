# Concrete Cook–Levin second-constraint first-literal second unary-unit step

`lean/PNP/Concrete/CookLevinBuilderSecondConstraintFirstLiteralSecondUnaryUnitStep.lean`
composes the complete second-constraint first-literal first-unary-unit step with the already audited
selected `T` appender and fixed unary cursor-advance table. Every raw input
emits exactly the second unary unit of the second constraint's first variable
index and advances the retained unary coordinate to that index's third unit.

The finite output is the complete four populated clauses of the first
constraint followed by the next constraint's `Sep`, positive-sign `T`, and two
unary `T` tokens. Rectangular
`none` padding is skipped by the canonical schedule emitter. The following
direct token opportunity is constructively proved to be another `T`: the third
unary unit of an index that is at least three. That third unary token is
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
`BuilderSecondConstraintFirstLiteralFirstUnaryUnitStep.machine` behind another total
nine-symbol bridge. The complete symbolic rule count is `4920` plus the sixteen
inherited and generated unary-evaluator rule counts. Only the final cursor
component supplies the global accept and reject states. The reused state
embeddings are injective, their images are disjoint, and the combined rule list
is pairwise query-distinct, so neither bridge can be shadowed.

## Exact trace and canonical output

`prefix_workRunExact` transports the full predecessor trace into the outer
first-state image. `prefixSecondUnaryUnit_launch_workStep` proves the outer bridge.
`appender_workRunExact` appends the selected second unary unit while preserving the
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

- `secondConstraintFirstLiteralSecondUnaryTokens_eq_canonical_formula_prefix` proves
  the finite output is a prefix of `encodeCNFTokens problem.formula`;
- `finalTokenBits_eq_encodedFormula_secondConstraintFirstLiteralSecondUnary` proves
  exact equality with `encodedFormula.take (2 * (FormulaWidth + 40))`;
- `nextTokenSlot_direct_eq_t` proves the retained coordinate contains the
  third unary `T`;
- `specification_secondUnaryUnit_step` and `specification_next_step` agree with the
  token-level cursor before and after the transition.

Writing `V = formulaVariableSlotBound`, `C = formulaTokensPerClause`, and
`Q = formulaClauseSlotsPerConstraint`, the final coordinate is

```text
V + 1 + Q * C + 4.
```

`finalOutside_contains_finalTokenSlot` proves that coordinate is retained as a
unary root in the preserved workspace.

## External compiled bound

The exact work count is the predecessor count, one outer launch, the selected
appender, one reused inner launch, and the complete cursor scan. The external
raw-transition polynomial evaluates to

```text
BuilderSecondConstraintFirstLiteralFirstUnaryUnitStep.rawTimeBound(n)
+ 570
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
emitted second unary `T`, retained third unary `T`, compiled acceptance, polynomial
evaluation, and every fail-closed boundary.

```sh
lake env lean -DwarningAsError=true \
  lean-audit/PNPConcreteCookLevinBuilderSecondConstraintFirstLiteralSecondUnaryUnitStepAxiomAudit.lean
lake env lean -DwarningAsError=true \
  lean-regression/PNPConcreteCookLevinBuilderSecondConstraintFirstLiteralSecondUnaryUnitStep.lean
node --test \
  audits/lean-concrete-cook-levin-builder-second-constraint-first-literal-second-unary-unit-step0.test.mjs
```

The combined audit covers all 48 public declarations in the new module plus
eight reviewed interfaces reused from the true-token/cursor suffix and its
dead-state boundary. Exactly 14 closures are empty, 11 use only `propext`, and
31 use only `propext` and `Quot.sound`. No declaration reaches a project axiom,
`Classical.choice`, `sorry`, `admit`, native/SAT shortcuts, host-side schedule
lookup, or a caller-supplied execution certificate.

## Generated publication artifacts

The compiled environment records inventory coordinate
`PNP-LEAN-THEOREM-INVENTORY-2026-07-23-73`: 10,587 declarations, 5,920
theorems, 3,344 assumption-free theorems, 4,043 excluded private declarations,
93 source-closure modules, and 1,581 reviewed milestone candidates. Its
8,132,004 canonical bytes have SHA-256
`232f95a1046a175eab3cecaaec3a0a9ed67515d123d407ddb08a813654d0f5a0`;
the Lean source-closure SHA-256 is
`f9b89038ba5eceee5e884ade0f8856cadef01ffa2513c5814c587e48820e2a59`.

Publication map coordinate `PNP-FORMAL-PUBLICATION-MAP-2026-07-23-73` has 53
milestones, of which 50 are earned and the same three global milestones remain
unearned, plus 1,581 exact kernel-type fingerprints. Its canonical reviewed-
object fingerprint is
`dec00862c3a4ffa08a8da32206f486b7a6f56e1503ed036d0b677ba70c9a9460`.
Its 491,484 canonical file bytes have SHA-256
`bc674f2bc27576f0a40252eea49eb1a9fa51e5d3d11d518649ed3a7d26f8d415`.

Status coordinate `PNP-FORMAL-RECONSTRUCTION-STATUS-2026-07-23-73` has
1,226,926 bytes and SHA-256
`62645e7d64131ca2f2e1cfd5e67f5c6eb011022b9982c6df7beb1157c477ee2b`.
The generated report coordinate is
`PNP-CANONICAL-FORMAL-RECONSTRUCTION-REPORT-2026-07-23-73`; its 114,678-byte
TeX has SHA-256
`825a9bf595288bc1f8021055c6965f5527c81c5b5a2b009c6d56698a350ec01a`,
and its 50-page, 367,190-byte PDF has SHA-256
`fd3eedb22d4720f9c9bd2ff78edad54769465e39367c32ed64a7607dd0a57154`.

All activation fingerprints remain unset, all four project assumptions and six
blockers remain, `PNP.Main.p_eq_np` remains absent, and the concrete publication
gate remains false.

## Remaining boundary

This is one fixed populated token transition and one unary cursor advance. It
does not emit the following third unary `T`, complete the second constraint's first
literal, traverse the second constraint, interpret arbitrary schedule
coordinates, implement a general dynamic formula cursor, emit the remaining
formula body, construct a complete raw formula builder, provide builder
`RawRefinement` or a `PolynomialReduction`, prove CNF-SAT NP-complete or in P,
or establish `PNP.Main.p_eq_np`.
