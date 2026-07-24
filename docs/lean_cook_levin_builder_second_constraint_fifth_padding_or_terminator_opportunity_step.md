# Concrete Cook–Levin second-constraint fifth padding-or-terminator opportunity

`lean/PNP/Concrete/CookLevinBuilderSecondConstraintFifthPaddingOrTerminatorOpportunityStep.lean`
adds one bounded schedule transition after the fourth padding-or-unary
opportunity following the second constraint's first literal. The represented
tableau width—not a host-side lookup and not a caller-supplied
certificate—selects the behavior:

- at width one, this schedule position is padding, so the machine consumes
  the opportunity without emitting a formula token;
- at every wider width, this position is the terminating `F` of the second
  literal, so the machine appends exactly that `F`.

Both branches advance the retained formula coordinate by one. The step does
not consume the following slot, complete the following literal, traverse the
second constraint, implement a general schedule cursor, or establish `P = NP`.

## Literal runtime branch

The suffix first evaluates the represented tape-width polynomial. The
existing unary-root controller consumes one unit from the evaluated root.
Its `done` exit takes a direct bridge to the token appender's accepting state,
leaving the output unchanged. Its `more` exit enters the same audited
appender rule table at the `F` request state.

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
machine has `5884` literal rules plus the twenty-eight inherited and current
unary-evaluator rule counts. The combined table is pairwise query-distinct,
its halt states are separated, and no rule is sourced at global acceptance.

## Exact trace and output

The proof composes these exact traces:

1. the complete fourth padding-or-unary-opportunity predecessor;
2. the width-polynomial evaluator;
3. the controller's width-one skip or wider-width launch;
4. zero appender steps at width one or exactly one `F` append otherwise;
5. the evaluator that materializes the following formula coordinate.

`secondConstraintFifthPaddingOrTerminatorTokens_eq_canonical_formula_prefix` proves
that the resulting token list is an exact prefix of the canonical Cook–Levin
formula. The work-tape bits satisfy

```text
encodeTokenPairs(output)
= encodedFormula.take
    (2 * (FormulaWidth + 43 + if tapeWidth = 1 then 0 else 5)).
```

Thus the width-one branch retains the predecessor's `FormulaWidth + 43`
tokens, while every wider branch has `FormulaWidth + 48` tokens.

`specification_opportunity_step` proves that the consumed opportunity agrees
with the direct formula cursor. The retained coordinate is

```text
formulaVariableSlotBound
+ 1
+ formulaClauseSlotsPerConstraint * formulaTokensPerClause
 + 12.
```

At that coordinate, `followingTokenSlot_direct_eq_padding_or_t` and
`specification_following_step` prove that the next slot is again padding at
width one and the opening unary `T` of the following literal at every wider
width. The machine observes and retains this boundary but does not consume
the following slot.

## External compiled bound

The raw-transition polynomial evaluates to

```text
BuilderSecondConstraintFourthPaddingOrUnaryOpportunityStep.rawTimeBound(n)
+ 660
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
`F` bridge. Exact traces, pairwise query distinction, halt separation, and
the no-rule-at-accept proof make bridge removal, shadowing, suffix
replacement, state collision, or malformed execution fail closed.

The dedicated axiom transcript prints all 66 public outer declarations, all
14 declarations of the new optional-terminator appender, and the two
strengthened terminator schedule lemmas. Every printed declaration must
remain within the approved Lean-standard closure; project axioms,
`Classical.choice`, `sorry`, `admit`, native or SAT shortcuts, host-side
schedule lookup, and caller certificates are rejected.
The measured kernel closure split is 37 empty, 12 `propext`, and 33
`propext`/`Quot.sound`.

```sh
lake env lean -DwarningAsError=true \
  lean-audit/PNPConcreteCookLevinBuilderSecondConstraintFifthPaddingOrTerminatorOpportunityStepAxiomAudit.lean
lake env lean -DwarningAsError=true \
  lean-regression/PNPConcreteCookLevinBuilderSecondConstraintFifthPaddingOrTerminatorOpportunityStep.lean
node --test \
  audits/lean-concrete-cook-levin-builder-second-constraint-fifth-padding-or-terminator-opportunity-step0.test.mjs
```

## Generated publication artifacts

The compiled environment records inventory coordinate
`PNP-LEAN-THEOREM-INVENTORY-2026-07-24-81`: 11,565 declarations, 6,685
theorems, 3,528 assumption-free theorems, 4,432 excluded private
declarations, 101 source-closure modules, and 1,874 reviewed milestone
candidates. Its 10,268,933 canonical bytes have SHA-256
`9bbe6b0ff34e766961f8687d77372eaad8834eee5e9ad4ea5b76ac65625e9e32`;
the Lean source-closure SHA-256 is
`70f4892088b59aafd74c6d28b03aea966106d3335c7dfcfe31d7b465b05fb302`.

Publication map coordinate `PNP-FORMAL-PUBLICATION-MAP-2026-07-24-81` has
61 milestones, of which 58 are earned and the same three global milestones
remain unearned, plus 1,874 exact kernel-type fingerprints. Its canonical
reviewed-object fingerprint is
`a0c1abf69d549e43bf0c994ca5ba7903f4f6f835b0d502dc877a0990ed4c4c4c`.
Its 607,630 file bytes have SHA-256
`12f1d588b35d4156aec74212c9e23284ec9658f9473fca2c07301d24e4f6bee0`.

Status coordinate `PNP-FORMAL-RECONSTRUCTION-STATUS-2026-07-24-81` has
1,490,990 bytes and SHA-256
`8c7c4a57293d04036e481b181c11f2f374d6c25089f3cabf4d154c69cb711caf`.
The generated report coordinate is
`PNP-CANONICAL-FORMAL-RECONSTRUCTION-REPORT-2026-07-24-81`; its 141,731-byte
TeX has SHA-256
`3a591ac0b52e987bc32022911783b2d8292fb0b9d602a85e5d81eadfc89cb4f8`,
and its 59-page, 394,451-byte PDF has SHA-256
`1c7c8771926ef276e2957ea72fc04ee1db4c3400c43cb42da8fbc05025972d6b`.

All five activation fingerprints remain unset, all four project assumptions
and six blockers remain, `PNP.Main.p_eq_np` remains absent, and the concrete
publication gate remains false.

## Remaining boundary

This milestone handles the fifth fixed width-dependent schedule
opportunity. It does not consume the next padding or opening-`T` slot,
complete the following literal, traverse the rest of the second constraint,
interpret arbitrary schedule coordinates, implement a general dynamic
formula cursor, emit the remaining formula body, construct a complete raw
formula builder, supply builder `RawRefinement` or a
`PolynomialReduction`, prove CNF-SAT NP-complete or in P, or establish
`PNP.Main.p_eq_np`.
