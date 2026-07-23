# Concrete Cook–Levin second-constraint first-literal terminator step

`lean/PNP/Concrete/CookLevinBuilderSecondConstraintFirstLiteralTerminatorStep.lean`
composes the complete third-unary-unit endpoint with the already audited
selected `F` appender and fixed unary cursor advance. Every raw input emits
exactly the terminator of the second constraint's first literal, the token `F`, and moves
the retained coordinate to the following formula-token opportunity.

The following token depends on the tableau width. When the tape width is one,
the at-least-one clause has no further literal and the next token is `Finish`.
At wider widths, the clause continues and the next token is the positive `T`
sign of another literal. The machine proves and retains that distinction; it
does not emit either following token.

## Literal composition

The suffix is reused unchanged from
`BuilderSecondClauseFirstLiteralPrefix.FalseTokenCursor.machine`. It consists
of the selected 59-rule false-token appender, a total nine-symbol bridge, and
the 45-rule cursor table:

```text
59 + 9 + 45 = 113 rules.
```

One outer `WorkChain` places that suffix after
`BuilderSecondConstraintFirstLiteralThirdUnaryUnitStep.machine` behind another
total nine-symbol bridge. The complete symbolic rule count is `5164` plus the
sixteen inherited and generated unary-evaluator rule counts. The final cursor
component alone supplies the global accept and reject states. The state images
are disjoint and the combined rule list is pairwise query-distinct, so neither
bridge can be shadowed.

## Exact trace and canonical output

`prefix_workRunExact` transports the full predecessor trace.
`prefixTerminator_launch_workStep` proves the outer bridge.
`appender_workRunExact` appends the selected `F` while preserving the raw
input, unary workspace, and exterior garbage.
`falseTokenCursor_launch_workStep` proves the inner bridge, and
`cursor_workRunExact` performs the complete bidirectional unary scan.
`suffix_workRunExact` and `workRunExact` compose those pieces into exact
all-input executions.

The constructive schedule proof identifies the first variable index as three
in both possible shapes of the second scheduled constraint. It then proves the
token sequence through the terminator and preserves the width-dependent next
token. Consequently:

- `secondConstraintFirstLiteralTerminatorTokens_eq_canonical_formula_prefix`
  proves the finite output is a prefix of `encodeCNFTokens problem.formula`;
- `finalTokenBits_eq_encodedFormula_secondConstraintFirstLiteralTerminator`
  proves exact equality with
  `encodedFormula.take (2 * (FormulaWidth + 42))`;
- `specification_terminator_step` proves the executed opportunity emits `F`;
- `nextTokenSlot_direct_eq_finish_or_t` and `specification_next_step` prove
  that the retained opportunity contains `Finish` exactly at width one and
  otherwise contains `T`.

Writing `V = formulaVariableSlotBound`, `C = formulaTokensPerClause`, and
`Q = formulaClauseSlotsPerConstraint`, the retained coordinate is

```text
V + 1 + Q * C + 6.
```

`finalOutside_contains_finalTokenSlot` proves that coordinate remains encoded
as a unary root in the preserved workspace.

## External compiled bound

The exact work count is the predecessor count, one outer launch, the selected
appender, one reused inner launch, and the complete cursor scan. The external
raw-transition polynomial evaluates to

```text
BuilderSecondConstraintFirstLiteralThirdUnaryUnitStep.rawTimeBound(n)
+ 594
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
all-zero and all-one words, input-only and paired verifiers, both width branches,
both bridge launches, exact final tape and token bits, `F` emission, retained
`Finish`/`T`, output prefix, coordinate, rule count, polynomial evaluation,
compiled acceptance, and every fail-closed boundary.

```sh
lake env lean -DwarningAsError=true \
  lean-audit/PNPConcreteCookLevinBuilderSecondConstraintFirstLiteralTerminatorStepAxiomAudit.lean
lake env lean -DwarningAsError=true \
  lean-regression/PNPConcreteCookLevinBuilderSecondConstraintFirstLiteralTerminatorStep.lean
node --test \
  audits/lean-concrete-cook-levin-builder-second-constraint-first-literal-terminator-step0.test.mjs
```

The combined audit covers all 48 public declarations in the new module plus
eight reviewed interfaces reused from the false-token/cursor suffix and its
dead-state boundary. Exactly 14 closures are empty, 11 use only `propext`, and
31 use only `propext` and `Quot.sound`. No declaration reaches a project axiom,
`Classical.choice`, `sorry`, `admit`, native/SAT shortcuts, host-side schedule
lookup, or a caller-supplied execution certificate.

## Generated publication artifacts

The compiled environment records inventory coordinate
`PNP-LEAN-THEOREM-INVENTORY-2026-07-23-75`: 10,775 declarations, 6,078
theorems, 3,366 assumption-free theorems, 4,194 excluded private declarations,
95 source-closure modules, and 1,649 reviewed milestone candidates. Its
8,525,418 canonical bytes have SHA-256
`62bbec37bb0277289e6c5affe7eb1496595b9ea18f2b184877e803a94aeff92b`;
the Lean source-closure SHA-256 is
`01a9a8f72146c4b58817807a6d9501f4f62bd639f010522032294f7fa556c594`.

Publication map coordinate `PNP-FORMAL-PUBLICATION-MAP-2026-07-23-75` has 55
milestones, of which 52 are earned and the same three global milestones remain
unearned, plus 1,649 exact kernel-type fingerprints. Its canonical reviewed-
object fingerprint is
`7628090d74eb9404f26766809b2a804b1d39c7eb4cb21aa28e4d0c9063a6237f`.
Its 517,939 canonical file bytes have SHA-256
`e5427f89c140823879dbb5aa56ffac61b9663226609dca1ad0b72b9cb32aaf81`.

Status coordinate `PNP-FORMAL-RECONSTRUCTION-STATUS-2026-07-23-75` has
1,291,094 bytes and SHA-256
`47656946dbc22a3813ee08102a65fdb63333c141dfd24a3990e935ebd8ffd3ae`.
The generated report coordinate is
`PNP-CANONICAL-FORMAL-RECONSTRUCTION-REPORT-2026-07-23-75`; its 120,589-byte
TeX has SHA-256
`098c7680d59b62b7d6a2e60bf7f58cc3407110777389fa23f7e0dad1205e64d7`,
and its 52-page, 373,108-byte PDF has SHA-256
`26183653c1f4fc5fe69bd762248fca3483d765c6cfe29426ed257de53b65536e`.

All five activation fingerprints remain unset, all four project assumptions
and six blockers remain, `PNP.Main.p_eq_np` remains absent, and the concrete
publication gate remains false.

## Remaining boundary

This is one fixed populated token transition and one unary cursor advance. It
does not emit the following `Finish` or `T`, emit the rest of the second
constraint, interpret arbitrary schedule coordinates, implement a general
dynamic formula cursor, emit the remaining formula body, construct a complete
raw formula builder, provide builder `RawRefinement` or a
`PolynomialReduction`, prove CNF-SAT NP-complete or in P, or establish
`PNP.Main.p_eq_np`.
