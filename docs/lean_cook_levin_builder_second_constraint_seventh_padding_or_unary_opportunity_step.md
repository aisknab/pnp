# Concrete Cook–Levin second-constraint seventh padding-or-unary opportunity

`lean/PNP/Concrete/CookLevinBuilderSecondConstraintSeventhPaddingOrUnaryOpportunityStep.lean`
adds one bounded schedule transition after the sixth padding-or-opening-unary
opportunity in the second constraint. The represented
tableau width—not a host-side lookup and not a caller-supplied
certificate—selects the behavior:

- at width one, this schedule position is padding, so the machine consumes
  the opportunity without emitting a formula token;
- at every wider width, this position is the first unary-index `T` of the
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
machine has `6124` literal rules plus the thirty-two inherited and current
unary-evaluator rule counts. The combined table is pairwise query-distinct,
its halt states are separated, and no rule is sourced at global acceptance.

## Exact trace and output

The proof composes these exact traces:

1. the complete sixth padding-or-opening-unary-opportunity predecessor;
2. the width-polynomial evaluator;
3. the controller's width-one skip or wider-width launch;
4. zero appender steps at width one or exactly one `T` append otherwise;
5. the evaluator that materializes the following formula coordinate.

`secondConstraintSeventhPaddingOrUnaryTokens_eq_canonical_formula_prefix` proves
that the resulting token list is an exact prefix of the canonical Cook–Levin
formula. The work-tape bits satisfy

```text
encodeTokenPairs(output)
= encodedFormula.take
    (2 * (FormulaWidth + 43 + if tapeWidth = 1 then 0 else 7)).
```

Thus the width-one branch retains the predecessor's `FormulaWidth + 43`
tokens, while every wider branch has `FormulaWidth + 50` tokens.

`specification_opportunity_step` proves that the consumed opportunity agrees
with the direct formula cursor. The retained coordinate is

```text
formulaVariableSlotBound
+ 1
+ formulaClauseSlotsPerConstraint * formulaTokensPerClause
+ 14.
```

At that coordinate, `followingTokenSlot_direct_eq_padding_or_t` and
`specification_following_step` prove that the next slot is again padding at
width one and the second unary-index `T` of the following literal at every
wider width. The machine observes and retains this boundary but does not
consume the following slot.

## External compiled bound

The raw-transition polynomial evaluates to

```text
BuilderSecondConstraintSixthPaddingOrOpeningUnaryOpportunityStep.rawTimeBound(n)
+ 684
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
  lean-audit/PNPConcreteCookLevinBuilderSecondConstraintSeventhPaddingOrUnaryOpportunityStepAxiomAudit.lean
lake env lean -DwarningAsError=true \
  lean-regression/PNPConcreteCookLevinBuilderSecondConstraintSeventhPaddingOrUnaryOpportunityStep.lean
node --test \
  audits/lean-concrete-cook-levin-builder-second-constraint-seventh-padding-or-unary-opportunity-step0.test.mjs
```

## Generated publication artifacts

The compiled environment records inventory coordinate
`PNP-LEAN-THEOREM-INVENTORY-2026-07-25-83`: 11,811 declarations, 6,873
theorems, 3,574 assumption-free theorems, 4,511 excluded private
declarations, 103 source-closure modules, and 1,944 reviewed milestone
candidates. Its 11,002,266 canonical bytes have SHA-256
`b5a96357624ad63fd3815db8be685ebb5a3d52cf8859d3621d392e966df18940`;
the Lean source-closure SHA-256 is
`203119b036adfbb429800396a175ae7e8e01ebd5e142e17a48d8724b7a5b9f9f`.

Publication map coordinate `PNP-FORMAL-PUBLICATION-MAP-2026-07-25-83` has
63 milestones, of which 60 are earned and the same three global milestones
remain unearned, plus 1,944 exact kernel-type fingerprints. Its canonical
reviewed-object fingerprint is
`1036c804208e5843a372510945c0da8b7773670730c5412abf722f5f66bfebf3`.
Its 637,704 file bytes have SHA-256
`f65f5cc9052072bf4aa726a7c19cfac9223964db896e67f304ebdf7d3ba89006`.

Status coordinate `PNP-FORMAL-RECONSTRUCTION-STATUS-2026-07-25-83` has
1,559,103 bytes and SHA-256
`0127bc63e11364312db37bcdbd50e672911d62edc5555ecccbefce6534aa65e5`.
The generated report coordinate is
`PNP-CANONICAL-FORMAL-RECONSTRUCTION-REPORT-2026-07-25-83`; its 149,920-byte
TeX has SHA-256
`59825734e578bd02212f30faf6ea64ef0bf31a131dff128cf1e722ec374ff622`,
and its 62-page, 401,311-byte PDF has SHA-256
`829716176063a0ab6b9ccb07bfe59aa9906aaceee20ff10c3edad31114a1367e`.

All five activation fingerprints remain unset, all four project assumptions
and six blockers remain, `PNP.Main.p_eq_np` remains absent, and the concrete
publication gate remains false.

## Remaining boundary

This milestone handles the seventh fixed width-dependent schedule
opportunity. It does not consume the next padding or second-unary-`T` slot,
complete the following literal, traverse the rest of the second constraint,
interpret arbitrary schedule coordinates, implement a general dynamic
formula cursor, emit the remaining formula body, construct a complete raw
formula builder, supply builder `RawRefinement` or a
`PolynomialReduction`, prove CNF-SAT NP-complete or in P, or establish
`PNP.Main.p_eq_np`.
