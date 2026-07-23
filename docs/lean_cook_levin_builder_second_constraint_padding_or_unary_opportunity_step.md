# Concrete Cook–Levin second-constraint padding-or-unary opportunity

`lean/PNP/Concrete/CookLevinBuilderSecondConstraintPaddingOrUnaryOpportunityStep.lean`
adds one bounded schedule transition after the width-selected successor of
the second constraint's first literal. The represented tableau width—not a
host-side lookup and not a caller-supplied certificate—selects the behavior:

- at width one, this schedule position is padding, so the machine consumes
  the opportunity without emitting a formula token;
- at every wider width, this position is the first unary `T` of the second
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
machine has `5404` literal rules plus the twenty inherited and current
unary-evaluator rule counts. The combined table is pairwise query-distinct,
its halt states are separated, and no rule is sourced at global acceptance.

## Exact trace and output

The proof composes these exact traces:

1. the complete width-selected successor-token predecessor;
2. the width-polynomial evaluator;
3. the controller's width-one skip or wider-width launch;
4. zero appender steps at width one or exactly one `T` append otherwise;
5. the evaluator that materializes the following formula coordinate.

`secondConstraintPaddingOrUnaryTokens_eq_canonical_formula_prefix` proves
that the resulting token list is an exact prefix of the canonical Cook–Levin
formula. The work-tape bits satisfy

```text
encodeTokenPairs(output)
= encodedFormula.take
    (2 * (FormulaWidth + 43 + if tapeWidth = 1 then 0 else 1)).
```

Thus the width-one branch retains the predecessor's `FormulaWidth + 43`
tokens, while every wider branch has `FormulaWidth + 44` tokens.

`specification_opportunity_step` proves that the consumed opportunity agrees
with the direct formula cursor. The retained coordinate is

```text
formulaVariableSlotBound
+ 1
+ formulaClauseSlotsPerConstraint * formulaTokensPerClause
+ 8.
```

At that coordinate, `followingTokenSlot_direct_eq_padding_or_t` and
`specification_following_step` prove that the next slot is again padding at
width one and the second unary `T` at every wider width. The machine observes
and retains this boundary but does not consume the following slot.

## External compiled bound

The raw-transition polynomial evaluates to

```text
BuilderSecondConstraintFirstLiteralSuccessorTokenStep.rawTimeBound(n)
+ 612
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

The dedicated axiom transcript prints all 80 public declarations in the new
module plus the two strengthened terminator schedule lemmas. Every printed
declaration must remain within the approved Lean-standard closure; project
axioms, `Classical.choice`, `sorry`, `admit`, native or SAT shortcuts,
host-side schedule lookup, and caller certificates are rejected.
The measured closure split is 37 empty, 12 `propext`-only, and 33
`propext`/`Quot.sound`.

```sh
lake env lean -DwarningAsError=true \
  lean-audit/PNPConcreteCookLevinBuilderSecondConstraintPaddingOrUnaryOpportunityStepAxiomAudit.lean
lake env lean -DwarningAsError=true \
  lean-regression/PNPConcreteCookLevinBuilderSecondConstraintPaddingOrUnaryOpportunityStep.lean
node --test \
  audits/lean-concrete-cook-levin-builder-second-constraint-padding-or-unary-opportunity-step0.test.mjs
```

## Generated publication artifacts

The compiled environment records inventory coordinate
`PNP-LEAN-THEOREM-INVENTORY-2026-07-23-77`: 11,055 declarations, 6,294
theorems, 3,428 assumption-free theorems, 4,278 excluded private
declarations, 97 source-closure modules, and 1,729 reviewed milestone
candidates. Its 9,048,234 canonical bytes have SHA-256
`b2c61b8afcac8df4e71b2f9dd53b779631347dbaac678db77c65113acbdd93b5`;
the Lean source-closure SHA-256 is
`c6213632859bace723f284a2c7d3722fd8e763f918ea310f0e4026a1e3917b48`.

Publication map coordinate `PNP-FORMAL-PUBLICATION-MAP-2026-07-23-77` has
57 milestones, of which 54 are earned and the same three global milestones
remain unearned, plus 1,729 exact kernel-type fingerprints. Its canonical
reviewed-object fingerprint is
`1947a557dff1909bb1c9b055ddc2393c8a1b7f05f70efdc32cf6c55f2f51af1c`.
Its 547,880 file bytes have SHA-256
`270af07378eca03dff852d1b9f70b034e058b63a8a0e24dd0257e5358ecf3a7b`.

Status coordinate `PNP-FORMAL-RECONSTRUCTION-STATUS-2026-07-23-77` has
1,356,442 bytes and SHA-256
`90475e52efd015aec577f1a378d95d520b89d3b20fe4c7bdfc4db7585c289af3`.
The generated report coordinate is
`PNP-CANONICAL-FORMAL-RECONSTRUCTION-REPORT-2026-07-23-77`; its 127,168-byte
TeX has SHA-256
`f6cde89712bcdfd6a1b9d0763e3b29db15d3b11883cc12da722b13f16edc9304`,
and its 55-page, 379,261-byte PDF has SHA-256
`4087f0069f2097d9119feb082d8988e70e7a70ed4797da405012afa68d84f5f3`.

All five activation fingerprints remain unset, all four project assumptions
and six blockers remain, `PNP.Main.p_eq_np` remains absent, and the concrete
publication gate remains false.

## Remaining boundary

This milestone handles one fixed width-dependent schedule opportunity. It
does not consume the next padding or unary slot, complete the second literal,
traverse the rest of the second constraint, interpret arbitrary schedule
coordinates, implement a general dynamic formula cursor, emit the remaining
formula body, construct a complete raw formula builder, supply builder
`RawRefinement` or a `PolynomialReduction`, prove CNF-SAT NP-complete or in
P, or establish `PNP.Main.p_eq_np`.
