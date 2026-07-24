# Concrete Cook–Levin second-constraint fourth padding-or-unary opportunity

`lean/PNP/Concrete/CookLevinBuilderSecondConstraintFourthPaddingOrUnaryOpportunityStep.lean`
adds one bounded schedule transition after the third padding-or-unary
opportunity following the second constraint's first literal. The represented
tableau width—not a host-side lookup and not a caller-supplied
certificate—selects the behavior:

- at width one, this schedule position is padding, so the machine consumes
  the opportunity without emitting a formula token;
- at every wider width, this position is the fourth unary `T` of the second
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
machine has `5764` literal rules plus the twenty-six inherited and current
unary-evaluator rule counts. The combined table is pairwise query-distinct,
its halt states are separated, and no rule is sourced at global acceptance.

## Exact trace and output

The proof composes these exact traces:

1. the complete third padding-or-unary-opportunity predecessor;
2. the width-polynomial evaluator;
3. the controller's width-one skip or wider-width launch;
4. zero appender steps at width one or exactly one `T` append otherwise;
5. the evaluator that materializes the following formula coordinate.

`secondConstraintFourthPaddingOrUnaryTokens_eq_canonical_formula_prefix` proves
that the resulting token list is an exact prefix of the canonical Cook–Levin
formula. The work-tape bits satisfy

```text
encodeTokenPairs(output)
= encodedFormula.take
    (2 * (FormulaWidth + 43 + if tapeWidth = 1 then 0 else 4)).
```

Thus the width-one branch retains the predecessor's `FormulaWidth + 43`
tokens, while every wider branch has `FormulaWidth + 47` tokens.

`specification_opportunity_step` proves that the consumed opportunity agrees
with the direct formula cursor. The retained coordinate is

```text
formulaVariableSlotBound
+ 1
+ formulaClauseSlotsPerConstraint * formulaTokensPerClause
 + 11.
```

At that coordinate, `followingTokenSlot_direct_eq_padding_or_f` and
`specification_following_step` prove that the next slot is again padding at
width one and the terminating `F` at every wider width. The machine observes
and retains this boundary but does not consume the following slot.

## External compiled bound

The raw-transition polynomial evaluates to

```text
BuilderSecondConstraintThirdPaddingOrUnaryOpportunityStep.rawTimeBound(n)
+ 648
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
  lean-audit/PNPConcreteCookLevinBuilderSecondConstraintFourthPaddingOrUnaryOpportunityStepAxiomAudit.lean
lake env lean -DwarningAsError=true \
  lean-regression/PNPConcreteCookLevinBuilderSecondConstraintFourthPaddingOrUnaryOpportunityStep.lean
node --test \
  audits/lean-concrete-cook-levin-builder-second-constraint-fourth-padding-or-unary-opportunity-step0.test.mjs
```

## Generated publication artifacts

The compiled environment records inventory coordinate
`PNP-LEAN-THEOREM-INVENTORY-2026-07-24-80`: 11,424 declarations, 6,576
theorems, 3,497 assumption-free theorems, 4,379 excluded private
declarations, 100 source-closure modules, and 1,834 reviewed milestone
candidates. Its 9,910,328 canonical bytes have SHA-256
`62be5d1a5ba1c7669efecbd407e7ed66a6f6a9245afb32bda27a6356d1989d0f`;
the Lean source-closure SHA-256 is
`2ba454458c36cd1bc1f82fc816aca8b5b87f011bfef113c66d3e1eeec689d065`.

Publication map coordinate `PNP-FORMAL-PUBLICATION-MAP-2026-07-24-80` has
60 milestones, of which 57 are earned and the same three global milestones
remain unearned, plus 1,834 exact kernel-type fingerprints. Its canonical
reviewed-object fingerprint is
`4027f35da3106cc34eabd372db753c9555a5794b9e6d1092775945c065ad31d8`.
Its 591,470 file bytes have SHA-256
`cbe54d948e705984152e0bb4895d295c1eb895af2293ae79b65f367d7cc0da39`.

Status coordinate `PNP-FORMAL-RECONSTRUCTION-STATUS-2026-07-24-80` has
1,456,748 bytes and SHA-256
`41af6809aa5cd02b6edc7f7698253b29275345d9a9a4bab16afcb03ae251ff46`.
The generated report coordinate is
`PNP-CANONICAL-FORMAL-RECONSTRUCTION-REPORT-2026-07-24-80`; its 137,622-byte
TeX has SHA-256
`fe90cef934814a20e0fdc18061911ea005f6b788135c856a3aa89dc084555fa4`,
and its 58-page, 390,704-byte PDF has SHA-256
`00335f3b3dd41e1480c0eafec61692269d2b3c8221a342fccf6fa421e69d8cb4`.

All five activation fingerprints remain unset, all four project assumptions
and six blockers remain, `PNP.Main.p_eq_np` remains absent, and the concrete
publication gate remains false.

## Remaining boundary

This milestone handles the fourth fixed width-dependent schedule
opportunity. It does not consume the next padding or terminating-`F` slot,
complete the second literal, traverse the rest of the second constraint,
interpret arbitrary schedule coordinates, implement a general dynamic
formula cursor, emit the remaining formula body, construct a complete raw
formula builder, supply builder `RawRefinement` or a
`PolynomialReduction`, prove CNF-SAT NP-complete or in P, or establish
`PNP.Main.p_eq_np`.
