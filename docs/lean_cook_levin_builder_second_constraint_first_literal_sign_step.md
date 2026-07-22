# Concrete Cook–Levin second-constraint first-literal sign step

`lean/PNP/Concrete/CookLevinBuilderSecondConstraintFirstLiteralSignStep.lean`
composes the complete second-constraint separator step with the already audited
selected `T` appender and fixed unary cursor-advance table. Every raw input
emits exactly the positive sign beginning the second constraint's first literal
and advances the retained unary coordinate to the literal's first index token.

The finite output is the complete four populated clauses of the first
constraint followed by the next constraint's `Sep` and one new `T`. Rectangular
`none` padding is skipped by the canonical schedule emitter. The following
direct token opportunity is constructively proved to be another `T`: the first
unary unit of the next constraint's nonzero first variable index. That unary
token is observed but is not emitted by this milestone.

## Literal composition

The suffix is reused unchanged from
`BuilderSecondClauseSecondLiteralPrefix.TrueTokenCursor.machine`. It consists
of the selected 59-rule true-token appender, a total nine-symbol bridge, and the
45-rule cursor table:

```text
59 + 9 + 45 = 113 rules.
```

One outer `WorkChain` places that suffix after
`BuilderSecondConstraintSeparatorStep.machine` behind another total
nine-symbol bridge. The complete symbolic rule count is `4676` plus the sixteen
inherited and generated unary-evaluator rule counts. Only the final cursor
component supplies the global accept and reject states. The reused state
embeddings are injective, their images are disjoint, and the combined rule list
is pairwise query-distinct, so neither bridge can be shadowed.

## Exact trace and canonical output

`prefix_workRunExact` transports the full predecessor trace into the outer
first-state image. `prefixSign_launch_workStep` proves the outer bridge.
`appender_workRunExact` appends the selected positive sign while preserving the
raw input, unary workspace, and exterior garbage.
`trueTokenCursor_launch_workStep` proves the inner bridge, and
`cursor_workRunExact` performs the complete bidirectional unary scan.
`suffix_workRunExact` and `workRunExact` compose those pieces into exact
all-input executions.

The constructive schedule proof handles both possible shapes of the second
scheduled constraint. When the tape rectangle has width one, its first literal
is the first head variable, whose index follows the nonempty symbol block. At
larger widths it is the blank-symbol variable at the next tape position. In
both cases the variable index is positive, so its unary encoding starts with
`T`. Consequently:

- `secondConstraintFirstLiteralSignTokens_eq_canonical_formula_prefix` proves
  the finite output is a prefix of `encodeCNFTokens problem.formula`;
- `finalTokenBits_eq_encodedFormula_secondConstraintFirstLiteralSign` proves
  exact equality with `encodedFormula.take (2 * (FormulaWidth + 38))`;
- `nextTokenSlot_direct_eq_t` proves the retained coordinate contains the
  first unary `T`;
- `specification_sign_step` and `specification_next_step` agree with the
  token-level cursor before and after the transition.

Writing `V = formulaVariableSlotBound`, `C = formulaTokensPerClause`, and
`Q = formulaClauseSlotsPerConstraint`, the final coordinate is

```text
V + 1 + Q * C + 2.
```

`finalOutside_contains_finalTokenSlot` proves that coordinate is retained as a
unary root in the preserved workspace.

## External compiled bound

The exact work count is the predecessor count, one outer launch, the selected
appender, one reused inner launch, and the complete cursor scan. The external
raw-transition polynomial evaluates to

```text
BuilderSecondConstraintSeparatorStep.rawTimeBound(n)
+ 546
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
emitted positive sign, retained unary `T`, compiled acceptance, polynomial
evaluation, and every fail-closed boundary.

```sh
lake env lean -DwarningAsError=true \
  lean-audit/PNPConcreteCookLevinBuilderSecondConstraintFirstLiteralSignStepAxiomAudit.lean
lake env lean -DwarningAsError=true \
  lean-regression/PNPConcreteCookLevinBuilderSecondConstraintFirstLiteralSignStep.lean
node --test \
  audits/lean-concrete-cook-levin-builder-second-constraint-first-literal-sign-step0.test.mjs
```

The combined audit covers all 48 public declarations in the new module plus
eight reviewed interfaces reused from the true-token/cursor suffix and its
dead-state boundary. Exactly 14 closures are empty, 11 use only `propext`, and
31 use only `propext` and `Quot.sound`. No declaration reaches a project axiom,
`Classical.choice`, `sorry`, `admit`, native/SAT shortcuts, host-side schedule
lookup, or a caller-supplied execution certificate.

## Generated publication artifacts

The compiled environment records inventory coordinate
`PNP-LEAN-THEOREM-INVENTORY-2026-07-22-71`: 10,399 declarations, 5,762
theorems, 3,322 assumption-free theorems, 3,899 excluded private declarations,
91 source-closure modules, and 1,513 reviewed milestone candidates. Its
7,743,009 canonical bytes have SHA-256
`b61b6522ea989d3935524d9e22e22b9602a7ac5653b75fe80130e24e9977e644`;
the Lean source-closure SHA-256 is
`b57f4f8ae54e49e97875f528ac53ad956ec749676376787cb9d13614d53b1e55`.

Publication map coordinate `PNP-FORMAL-PUBLICATION-MAP-2026-07-22-71` has 51
milestones, of which 48 are earned and the same three global milestones remain
unearned, plus 1,513 exact kernel-type fingerprints. Its canonical reviewed-
object fingerprint is
`535db2ec32a6fe6133de83e4c13b168b1bf257b494cb031cf4f1fe89c61bdb02`.
Its 464,914 canonical file bytes have SHA-256
`4640f421da17f2922b71a07f427d85c11222f573df3a5ed0a427b2871fecdf87`.

Status coordinate `PNP-FORMAL-RECONSTRUCTION-STATUS-2026-07-22-71` has
1,162,705 bytes and SHA-256
`c6bb3a1935a1a1a75d6fd17afe4a2d96a973e4903cf3e3837f92facff5920e39`.
The generated report coordinate is
`PNP-CANONICAL-FORMAL-RECONSTRUCTION-REPORT-2026-07-22-71`; its 106,644-byte
TeX has SHA-256
`9b2e3cecd1afef26279b199c33c7aef00b0b870f652aadfceae1ee1ba46cbb74`,
and its 48-page, 362,183-byte PDF has SHA-256
`ef8e05bd907830ec8cc886c01764183e9788a439ea06f856d6f9e9529e2a3832`.

All activation fingerprints remain unset, all four project assumptions and six
blockers remain, `PNP.Main.p_eq_np` remains absent, and the concrete publication
gate remains false.

## Remaining boundary

This is one fixed populated token transition and one unary cursor advance. It
does not emit the following unary `T`, complete the second constraint's first
literal, traverse the second constraint, interpret arbitrary schedule
coordinates, implement a general dynamic formula cursor, emit the remaining
formula body, construct a complete raw formula builder, provide builder
`RawRefinement` or a `PolynomialReduction`, prove CNF-SAT NP-complete or in P,
or establish `PNP.Main.p_eq_np`.
