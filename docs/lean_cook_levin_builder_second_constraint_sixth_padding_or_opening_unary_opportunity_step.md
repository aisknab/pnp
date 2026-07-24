# Concrete Cook–Levin second-constraint sixth padding-or-opening-unary opportunity

`lean/PNP/Concrete/CookLevinBuilderSecondConstraintSixthPaddingOrOpeningUnaryOpportunityStep.lean`
adds one bounded schedule transition after the fifth padding-or-terminator
opportunity after the second constraint's completed second literal. The represented
tableau width—not a host-side lookup and not a caller-supplied
certificate—selects the behavior:

- at width one, this schedule position is padding, so the machine consumes
  the opportunity without emitting a formula token;
- at every wider width, this position is the opening positive `T` of the
  following literal, so the machine appends exactly that `T`.

Both branches advance the retained formula coordinate by one. The step does
not consume the following slot, finish the following literal, traverse the
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
machine has `6004` literal rules plus the thirty inherited and current
unary-evaluator rule counts. The combined table is pairwise query-distinct,
its halt states are separated, and no rule is sourced at global acceptance.

## Exact trace and output

The proof composes these exact traces:

1. the complete fifth padding-or-terminator-opportunity predecessor;
2. the width-polynomial evaluator;
3. the controller's width-one skip or wider-width launch;
4. zero appender steps at width one or exactly one `T` append otherwise;
5. the evaluator that materializes the following formula coordinate.

`secondConstraintSixthPaddingOrOpeningUnaryTokens_eq_canonical_formula_prefix` proves
that the resulting token list is an exact prefix of the canonical Cook–Levin
formula. The work-tape bits satisfy

```text
encodeTokenPairs(output)
= encodedFormula.take
    (2 * (FormulaWidth + 43 + if tapeWidth = 1 then 0 else 6)).
```

Thus the width-one branch retains the predecessor's `FormulaWidth + 43`
tokens, while every wider branch has `FormulaWidth + 49` tokens.

`specification_opportunity_step` proves that the consumed opportunity agrees
with the direct formula cursor. The retained coordinate is

```text
formulaVariableSlotBound
+ 1
+ formulaClauseSlotsPerConstraint * formulaTokensPerClause
 + 13.
```

At that coordinate, `followingTokenSlot_direct_eq_padding_or_t` and
`specification_following_step` prove that the next slot is again padding at
width one and the first unary-index `T` of the following literal at every wider width. The machine observes
and retains this boundary but does not consume the following slot.

## External compiled bound

The raw-transition polynomial evaluates to

```text
BuilderSecondConstraintFifthPaddingOrTerminatorOpportunityStep.rawTimeBound(n)
+ 672
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
  lean-audit/PNPConcreteCookLevinBuilderSecondConstraintSixthPaddingOrOpeningUnaryOpportunityStepAxiomAudit.lean
lake env lean -DwarningAsError=true \
  lean-regression/PNPConcreteCookLevinBuilderSecondConstraintSixthPaddingOrOpeningUnaryOpportunityStep.lean
node --test \
  audits/lean-concrete-cook-levin-builder-second-constraint-sixth-padding-or-opening-unary-opportunity-step0.test.mjs
```

## Generated publication artifacts

The compiled environment records inventory coordinate
`PNP-LEAN-THEOREM-INVENTORY-2026-07-24-82`: 11,688 declarations, 6,779
theorems, 3,551 assumption-free theorems, 4,464 excluded private
declarations, 102 source-closure modules, and 1,909 reviewed milestone
candidates. Its 10,624,262 canonical bytes have SHA-256
`4b4a9c4f2982960ee647e782b901afb71464fc037893282bf2b11603bb509028`;
the Lean source-closure SHA-256 is
`20d430cdd1fdca800d118ffcc7e487fc743dca5b4c5f170dc868384ed3d31d90`.

Publication map coordinate `PNP-FORMAL-PUBLICATION-MAP-2026-07-24-82` has
62 milestones, of which 59 are earned and the same three global milestones
remain unearned, plus 1,909 exact kernel-type fingerprints. Its canonical
reviewed-object fingerprint is
`d9458a79024b2fb2c973ec6dff894dade792755fe48b5fa64076f5a80bc1c9b9`.
Its 622,807 file bytes have SHA-256
`8806fe4b0b1e39d3d7148329de3e7879d42dcd475ce30b8059b808c8a33aae48`.

Status coordinate `PNP-FORMAL-RECONSTRUCTION-STATUS-2026-07-24-82` has
1,525,223 bytes and SHA-256
`98eae41f9e2a74bb6503b7c8532d179d847ef3ff8b63ba3acfa2c56a57b7cd88`.
The generated report coordinate is
`PNP-CANONICAL-FORMAL-RECONSTRUCTION-REPORT-2026-07-24-82`; its 145,814-byte
TeX has SHA-256
`b0820e4023da743a8c9da98c2c8daf9a1dcbb4753d82ca8f08164075f1962b82`,
and its 60-page, 397,740-byte PDF has SHA-256
`22419b6e80a4a24c29c6cd0109224fe8f0c0b385a174e8e37bdb69186c4e3e3d`.

All five activation fingerprints remain unset, all four project assumptions
and six blockers remain, `PNP.Main.p_eq_np` remains absent, and the concrete
publication gate remains false.

## Remaining boundary

This milestone handles the sixth fixed width-dependent schedule
opportunity. It does not consume the next padding or first-unary-`T` slot,
complete the following literal, traverse the rest of the second constraint,
interpret arbitrary schedule coordinates, implement a general dynamic
formula cursor, emit the remaining formula body, construct a complete raw
formula builder, supply builder `RawRefinement` or a
`PolynomialReduction`, prove CNF-SAT NP-complete or in P, or establish
`PNP.Main.p_eq_np`.
