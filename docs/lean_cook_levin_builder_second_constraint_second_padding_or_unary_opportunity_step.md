# Concrete Cook–Levin second-constraint second padding-or-unary opportunity

`lean/PNP/Concrete/CookLevinBuilderSecondConstraintSecondPaddingOrUnaryOpportunityStep.lean`
adds one bounded schedule transition after the first padding-or-unary
opportunity following the second constraint's first literal. The represented
tableau width—not a host-side lookup and not a caller-supplied
certificate—selects the behavior:

- at width one, this schedule position is padding, so the machine consumes
  the opportunity without emitting a formula token;
- at every wider width, this position is the second unary `T` of the second
  literal, so the machine appends exactly that `T`.

Both branches advance the retained formula coordinate by one. The step does
not consume the following slot, finish the second literal, traverse the
second constraint, implement a general schedule cursor, or establish
`P = NP`.

## Literal runtime branch

The suffix first evaluates the represented tape-width polynomial. The
existing unary-root controller consumes one unit from the evaluated root.
Its `done` exit takes a direct bridge to the token appender's accepting state,
leaving the output unchanged. Its `more` exit enters the same audited
appender at the `T` request state.

The optional-appender table contains:

```text
9 width-one skip bridge rules
+ 16 controller rules
+ 9 wider-width launch bridge rules
+ 59 token-appender rules
= 93 rules.
```

Three outer nine-symbol `WorkChain` bridges compose the predecessor, width
evaluator, optional appender, and retained-coordinate evaluator. The complete
machine has `5524` literal rules plus the twenty-two inherited and current
unary-evaluator rule counts. The combined table is pairwise query-distinct,
its halt states are separated, and no rule is sourced at global acceptance.

## Exact trace and output

The proof composes these exact traces:

1. the complete first padding-or-unary-opportunity predecessor;
2. the width-polynomial evaluator;
3. the controller's width-one skip or wider-width launch;
4. zero appender steps at width one or exactly one `T` append otherwise;
5. the evaluator that materializes the following formula coordinate.

`secondConstraintSecondPaddingOrUnaryTokens_eq_canonical_formula_prefix` proves
that the resulting token list is an exact prefix of the canonical Cook–Levin
formula. The work-tape bits satisfy

```text
encodeTokenPairs(output)
= encodedFormula.take
    (2 * (FormulaWidth + 43 + if tapeWidth = 1 then 0 else 2)).
```

Thus the width-one branch retains the predecessor's `FormulaWidth + 43`
tokens, while every wider branch has `FormulaWidth + 45` tokens.

`specification_opportunity_step` proves that the consumed opportunity agrees
with the direct formula cursor. The retained coordinate is

```text
formulaVariableSlotBound
+ 1
+ formulaClauseSlotsPerConstraint * formulaTokensPerClause
+ 9.
```

At that coordinate, `followingTokenSlot_direct_eq_padding_or_t` and
`specification_following_step` prove that the next slot is again padding at
width one and the third unary `T` at every wider width. The machine observes
and retains this boundary but does not consume the following slot.

## External compiled bound

The raw-transition polynomial evaluates to

```text
BuilderSecondConstraintPaddingOrUnaryOpportunityStep.rawTimeBound(n)
+ 624
+ 24*n
+ 12*FormulaWidth
+ 12*width
+ 12*widthRootPrefixLength
+ 6*widthWorkSteps
+ 6*targetWorkSteps.
```

`rawTimeBound_le` proves that this bounds six times the exact work trace. The
compiled interfaces prove exact execution, polynomial-fuel execution,
ordinary-start blank equivalence, acceptance, and non-timeout.

## Fail-closed boundary and audit

The predecessor endpoint is nonhalting before its launch bridge, and
one-step-short total fuel remains timeout. The width-one branch cannot enter
the token appender, while the wider branch must enter it through the selected
`T` bridge. Exact traces, pairwise query distinction, halt separation, and
the no-rule-at-accept proof make bridge removal, shadowing, suffix
replacement, state collision, or malformed execution fail closed.

The dedicated axiom transcript prints all 66 public declarations in the new
module, all 14 declarations of the reused optional appender, and the two
strengthened terminator schedule lemmas. Every printed declaration must
remain within the approved Lean-standard closure; project axioms,
`Classical.choice`, `sorry`, `admit`, native or SAT shortcuts, host-side
schedule lookup, and caller certificates are rejected.
The measured closure split is 37 empty, 12 `propext`-only, and 33
`propext`/`Quot.sound`.

```sh
lake env lean -DwarningAsError=true \
  lean-audit/PNPConcreteCookLevinBuilderSecondConstraintSecondPaddingOrUnaryOpportunityStepAxiomAudit.lean
lake env lean -DwarningAsError=true \
  lean-regression/PNPConcreteCookLevinBuilderSecondConstraintSecondPaddingOrUnaryOpportunityStep.lean
node --test \
  audits/lean-concrete-cook-levin-builder-second-constraint-second-padding-or-unary-opportunity-step0.test.mjs
```

## Generated publication artifacts

The compiled environment records inventory coordinate
`PNP-LEAN-THEOREM-INVENTORY-2026-07-23-78`: 11,178 declarations, 6,388
theorems, 3,451 assumption-free theorems, 4,308 excluded private
declarations, 98 source-closure modules, and 1,764 reviewed milestone
candidates. Its 9,315,791 canonical bytes have SHA-256
`3c9fd0f32bd9678eb7de0c5c41544582f16931b2c9c3a3e05da91ae6ff514fd9`;
the Lean source-closure SHA-256 is
`e4a252b5035528e0751fa447bacedc95e569d2477b4e5e81d9571052bd8ef347`.

Publication map coordinate `PNP-FORMAL-PUBLICATION-MAP-2026-07-23-78` has
58 milestones, of which 55 are earned and the same three global milestones
remain unearned, plus 1,764 exact kernel-type fingerprints. Its canonical
reviewed-object fingerprint is
`6750385dbcff87778b8cb45f19cbbd08de1e153656e2e6b7572b048e086eff7b`.
Its 562,427 file bytes have SHA-256
`7f312d2fecaf087c4c4a4b210ccf67c8ae1f842899bb9353decc93d7b05ca7a0`.

Status coordinate `PNP-FORMAL-RECONSTRUCTION-STATUS-2026-07-23-78` has
1,389,900 bytes and SHA-256
`651ae30751179c9a5361d5be0e45dc3a6c21e51c4d5e9d72d42a43e16b69fd6f`.
The generated report coordinate is
`PNP-CANONICAL-FORMAL-RECONSTRUCTION-REPORT-2026-07-23-78`; its 131,589-byte
TeX has SHA-256
`836a58715d14de6f49ac53de3224e96d0682e07fdc9f1e0978c226cee247cbc8`,
and its 56-page, 384,804-byte PDF has SHA-256
`69ba1b8ea33b5298171f03a6c53296207620706a1c4ccdc0faa230af18235290`.

All five activation fingerprints remain unset, all four project assumptions
and six blockers remain, `PNP.Main.p_eq_np` remains absent, and the concrete
publication gate remains false.

## Remaining boundary

This milestone handles the second fixed width-dependent schedule
opportunity. It does not consume the next padding or third-unary slot,
complete the second literal, traverse the rest of the second constraint,
interpret arbitrary schedule coordinates, implement a general dynamic
formula cursor, emit the remaining formula body, construct a complete raw
formula builder, supply builder `RawRefinement` or a
`PolynomialReduction`, prove CNF-SAT NP-complete or in P, or establish
`PNP.Main.p_eq_np`.
