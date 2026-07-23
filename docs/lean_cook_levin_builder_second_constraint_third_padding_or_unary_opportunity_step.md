# Concrete Cook–Levin second-constraint third padding-or-unary opportunity

`lean/PNP/Concrete/CookLevinBuilderSecondConstraintThirdPaddingOrUnaryOpportunityStep.lean`
adds one bounded schedule transition after the second padding-or-unary
opportunity following the second constraint's first literal. The represented
tableau width—not a host-side lookup and not a caller-supplied
certificate—selects the behavior:

- at width one, this schedule position is padding, so the machine consumes
  the opportunity without emitting a formula token;
- at every wider width, this position is the third unary `T` of the second
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
machine has `5644` literal rules plus the twenty-four inherited and current
unary-evaluator rule counts. The combined table is pairwise query-distinct,
its halt states are separated, and no rule is sourced at global acceptance.

## Exact trace and output

The proof composes these exact traces:

1. the complete second padding-or-unary-opportunity predecessor;
2. the width-polynomial evaluator;
3. the controller's width-one skip or wider-width launch;
4. zero appender steps at width one or exactly one `T` append otherwise;
5. the evaluator that materializes the following formula coordinate.

`secondConstraintThirdPaddingOrUnaryTokens_eq_canonical_formula_prefix` proves
that the resulting token list is an exact prefix of the canonical Cook–Levin
formula. The work-tape bits satisfy

```text
encodeTokenPairs(output)
= encodedFormula.take
    (2 * (FormulaWidth + 43 + if tapeWidth = 1 then 0 else 3)).
```

Thus the width-one branch retains the predecessor's `FormulaWidth + 43`
tokens, while every wider branch has `FormulaWidth + 46` tokens.

`specification_opportunity_step` proves that the consumed opportunity agrees
with the direct formula cursor. The retained coordinate is

```text
formulaVariableSlotBound
+ 1
+ formulaClauseSlotsPerConstraint * formulaTokensPerClause
+ 10.
```

At that coordinate, `followingTokenSlot_direct_eq_padding_or_t` and
`specification_following_step` prove that the next slot is again padding at
width one and the fourth unary `T` at every wider width. The machine observes
and retains this boundary but does not consume the following slot.

## External compiled bound

The raw-transition polynomial evaluates to

```text
BuilderSecondConstraintSecondPaddingOrUnaryOpportunityStep.rawTimeBound(n)
+ 636
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
  lean-audit/PNPConcreteCookLevinBuilderSecondConstraintThirdPaddingOrUnaryOpportunityStepAxiomAudit.lean
lake env lean -DwarningAsError=true \
  lean-regression/PNPConcreteCookLevinBuilderSecondConstraintThirdPaddingOrUnaryOpportunityStep.lean
node --test \
  audits/lean-concrete-cook-levin-builder-second-constraint-third-padding-or-unary-opportunity-step0.test.mjs
```

## Generated publication artifacts

The compiled environment records inventory coordinate
`PNP-LEAN-THEOREM-INVENTORY-2026-07-24-79`: 11,301 declarations, 6,482
theorems, 3,474 assumption-free theorems, 4,349 excluded private
declarations, 99 source-closure modules, and 1,799 reviewed milestone
candidates. Its 9,602,557 canonical bytes have SHA-256
`92ef59b6942817af4007241dd9716264c7f2c876f1b9abd8ad983977de725764`;
the Lean source-closure SHA-256 is
`15c3038cde96ace23dc91e97f5068a46669b5d3f8a50981609f6841599f61a1f`.

Publication map coordinate `PNP-FORMAL-PUBLICATION-MAP-2026-07-24-79` has
59 milestones, of which 56 are earned and the same three global milestones
remain unearned, plus 1,799 exact kernel-type fingerprints. Its canonical
reviewed-object fingerprint is
`542924b70dca9dc98c64d58c7003fc6c7cd916576b1d1fa72913cbbf32eb84b4`.
Its 576,913 file bytes have SHA-256
`9bdfd55e7d5f2753b4d0d08b51b20cfb2c40d64c124b3ea4586f0aa7ff459166`.

Status coordinate `PNP-FORMAL-RECONSTRUCTION-STATUS-2026-07-24-79` has
1,423,283 bytes and SHA-256
`7e32b25942a24a17e0c7ff9ecf2600cc2d7f2bb8dca1e79f9564e78411666a23`.
The generated report coordinate is
`PNP-CANONICAL-FORMAL-RECONSTRUCTION-REPORT-2026-07-24-79`; its 134,641-byte
TeX has SHA-256
`53cd06f71c02a18352b5f0156f43d3fd9bacdc16b9df8878fd779c519b02bb2d`,
and its 57-page, 387,864-byte PDF has SHA-256
`b98d273aba849c1f6e8705ab1334c46623165edcdbec739c8909fe871302bd7c`.

All five activation fingerprints remain unset, all four project assumptions
and six blockers remain, `PNP.Main.p_eq_np` remains absent, and the concrete
publication gate remains false.

## Remaining boundary

This milestone handles the third fixed width-dependent schedule
opportunity. It does not consume the next padding or fourth-unary slot,
complete the second literal, traverse the rest of the second constraint,
interpret arbitrary schedule coordinates, implement a general dynamic
formula cursor, emit the remaining formula body, construct a complete raw
formula builder, supply builder `RawRefinement` or a
`PolynomialReduction`, prove CNF-SAT NP-complete or in P, or establish
`PNP.Main.p_eq_np`.
