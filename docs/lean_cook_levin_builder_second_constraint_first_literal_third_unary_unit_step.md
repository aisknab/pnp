# Concrete Cook–Levin second-constraint first-literal third unary-unit step

`lean/PNP/Concrete/CookLevinBuilderSecondConstraintFirstLiteralThirdUnaryUnitStep.lean`
composes the complete second-constraint first-literal second-unary-unit step
with the already audited selected `T` appender and fixed unary cursor-advance
table. Every raw input emits exactly the third unary unit of the second constraint's
first variable index and advances the retained unary coordinate
to the following terminating `F`.

The finite output is the complete four populated clauses of the first
constraint followed by the next constraint's `Sep`, positive-sign `T`, and all
three unary `T` tokens encoding variable index three. Rectangular `none`
padding is skipped by the canonical schedule emitter. The following direct
token opportunity is constructively proved to be `F`, the terminator of that
literal. That `F` is observed but is not emitted by this milestone.

## Literal composition

The suffix is reused unchanged from
`BuilderSecondClauseSecondLiteralPrefix.TrueTokenCursor.machine`. It consists
of the selected 59-rule true-token appender, a total nine-symbol bridge, and the
45-rule cursor table:

```text
59 + 9 + 45 = 113 rules.
```

One outer `WorkChain` places that suffix after
`BuilderSecondConstraintFirstLiteralSecondUnaryUnitStep.machine` behind another
total nine-symbol bridge. The complete symbolic rule count is `5042` plus the
sixteen inherited and generated unary-evaluator rule counts. Only the final
cursor component supplies the global accept and reject states. The reused
state embeddings are injective, their images are disjoint, and the combined
rule list is pairwise query-distinct, so neither bridge can be shadowed.

## Exact trace and canonical output

`prefix_workRunExact` transports the full predecessor trace into the outer
first-state image. `prefixThirdUnaryUnit_launch_workStep` proves the outer
bridge. `appender_workRunExact` appends the selected third unary unit while
preserving the raw input, unary workspace, and exterior garbage.
`trueTokenCursor_launch_workStep` proves the inner bridge, and
`cursor_workRunExact` performs the complete bidirectional unary scan.
`suffix_workRunExact` and `workRunExact` compose those pieces into exact
all-input executions.

The constructive schedule proof handles both possible shapes of the second
scheduled constraint and identifies the variable index exactly. When the tape
rectangle has width one, `timeBound = 0` and the first head variable has index
three. At larger widths, the first literal is the blank-symbol variable at tape
position one, whose finite index also has value three. The scheduled clause
therefore begins `Sep, T, T, T, T, F`: one positive sign, three unary units,
and the terminating false token. Consequently:

- `secondConstraintFirstLiteralThirdUnaryTokens_eq_canonical_formula_prefix`
  proves the finite output is a prefix of `encodeCNFTokens problem.formula`;
- `finalTokenBits_eq_encodedFormula_secondConstraintFirstLiteralThirdUnary`
  proves exact equality with
  `encodedFormula.take (2 * (FormulaWidth + 41))`;
- `nextTokenSlot_direct_eq_f` proves the retained coordinate contains the
  terminating `F`;
- `specification_thirdUnaryUnit_step` and `specification_next_step` agree with
  the token-level cursor before and after the transition.

Writing `V = formulaVariableSlotBound`, `C = formulaTokensPerClause`, and
`Q = formulaClauseSlotsPerConstraint`, the final coordinate is

```text
V + 1 + Q * C + 5.
```

`finalOutside_contains_finalTokenSlot` proves that coordinate is retained as a
unary root in the preserved workspace.

## External compiled bound

The exact work count is the predecessor count, one outer launch, the selected
appender, one reused inner launch, and the complete cursor scan. The external
raw-transition polynomial evaluates to

```text
BuilderSecondConstraintFirstLiteralSecondUnaryUnitStep.rawTimeBound(n)
+ 582
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
emitted third unary `T`, retained terminating `F`, compiled acceptance,
polynomial evaluation, and every fail-closed boundary.

```sh
lake env lean -DwarningAsError=true \
  lean-audit/PNPConcreteCookLevinBuilderSecondConstraintFirstLiteralThirdUnaryUnitStepAxiomAudit.lean
lake env lean -DwarningAsError=true \
  lean-regression/PNPConcreteCookLevinBuilderSecondConstraintFirstLiteralThirdUnaryUnitStep.lean
node --test \
  audits/lean-concrete-cook-levin-builder-second-constraint-first-literal-third-unary-unit-step0.test.mjs
```

The combined audit covers all 48 public declarations in the new module plus
eight reviewed interfaces reused from the true-token/cursor suffix and its
dead-state boundary. Exactly 14 closures are empty, 11 use only `propext`, and
31 use only `propext` and `Quot.sound`. No declaration reaches a project axiom,
`Classical.choice`, `sorry`, `admit`, native/SAT shortcuts, host-side schedule
lookup, or a caller-supplied execution certificate.

## Generated publication artifacts

The compiled environment records inventory coordinate
`PNP-LEAN-THEOREM-INVENTORY-2026-07-23-74`: 10,681 declarations, 5,999
theorems, 3,355 assumption-free theorems, 4,118 excluded private declarations,
94 source-closure modules, and 1,615 reviewed milestone candidates. Its
8,326,497 canonical bytes have SHA-256
`d563b23ed13c17b531c108e1123fa3f9335b0ae4cccced90a8615bbe8c3a0325`;
the Lean source-closure SHA-256 is
`73b56e740058a4e9bd77715f9cfea0eeba4f280587d5dcab2101f7c27cf0a773`.

Publication map coordinate `PNP-FORMAL-PUBLICATION-MAP-2026-07-23-74` has 54
milestones, of which 51 are earned and the same three global milestones remain
unearned, plus 1,615 exact kernel-type fingerprints. Its canonical reviewed-
object fingerprint is
`b5c8c2ce0a23c9f24a4d4897aa4629c2fe1a095a555f6e7e71fd87a6cf2cffe2`.
Its 504,853 canonical file bytes have SHA-256
`076c91c7f8e1909f592eec69ccd5ba9b8780de56735427fde53228073955dc22`.

Status coordinate `PNP-FORMAL-RECONSTRUCTION-STATUS-2026-07-23-74` has
1,259,297 bytes and SHA-256
`c42cb2c616c7b59f2791a3745b95cc35ae218ccd44c358e70068b33775600348`.
The generated report coordinate is
`PNP-CANONICAL-FORMAL-RECONSTRUCTION-REPORT-2026-07-23-74`; its 117,167-byte
TeX has SHA-256
`283eb9e70e3743a8001a3e29af1c96f4bdbb2a831914bf4aa7165e73d8f7f0c3`,
and its 51-page, 371,445-byte PDF has SHA-256
`fbd2a0c7b88b2506c5ff699b3c36f068292bd3826109c58a5783f451b655a5b0`.

All activation fingerprints remain unset, all four project assumptions and six
blockers remain, `PNP.Main.p_eq_np` remains absent, and the concrete publication
gate remains false.

## Remaining boundary

This is one fixed populated token transition and one unary cursor advance. It
does not emit the following terminating `F`, complete the second constraint's
first literal, traverse the second constraint, interpret arbitrary schedule
coordinates, implement a general dynamic formula cursor, emit the remaining
formula body, construct a complete raw formula builder, provide builder
`RawRefinement` or a `PolynomialReduction`, prove CNF-SAT NP-complete or in P,
or establish `PNP.Main.p_eq_np`.
