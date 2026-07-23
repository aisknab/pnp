# Concrete Cook–Levin second-constraint first-literal successor token

`lean/PNP/Concrete/CookLevinBuilderSecondConstraintFirstLiteralSuccessorTokenStep.lean`
adds one bounded runtime branch after the terminator of the second
constraint's first literal. The represented tableau width—not a host-side
lookup and not a caller-supplied certificate—selects the token:

- at width one, the completed literal also completes the clause, so the
  machine appends `Finish`;
- at every wider width, another positive literal follows, so the machine
  appends `T`.

It emits exactly that one token. It does not emit the following opportunity,
complete the next literal, traverse the second constraint, implement a
general schedule cursor, or establish `P = NP`.

## Literal runtime branch

The suffix first evaluates the represented tape-width polynomial. The
existing unary-root controller then consumes one unit from the evaluated
root. Its `done` exit enters the audited token appender at the `Finish`
request state; its `more` exit enters the same appender at the `T` request
state. This uses one appender table rather than duplicating the 59 literal
rules.

The width branch contains:

```text
9 done-branch bridge rules
+ 16 controller rules
+ 9 more-branch bridge rules
+ 59 token-appender rules
= 93 rules.
```

Three total nine-symbol `WorkChain` bridges compose the predecessor, width
evaluator, runtime branch, and retained-coordinate evaluator. The complete
literal rule count is `5284` plus the sixteen inherited unary-evaluator
counts and the two new unary-evaluator counts. The combined table is
pairwise query-distinct, its halt states are separated, and no rule is
sourced at global acceptance.

## Exact trace and output

The proof composes these exact traces:

1. the complete first-literal terminator predecessor;
2. the width-polynomial evaluator;
3. the controller's width-one or wider branch;
4. exactly one `Finish` or `T` append;
5. the evaluator that materializes the following formula coordinate.

`secondConstraintFirstLiteralSuccessorTokens_eq_canonical_formula_prefix`
proves that the resulting token list is an exact prefix of the canonical
Cook–Levin formula. The work-tape bits satisfy

```text
encodeTokenPairs(output)
= encodedFormula.take (2 * (FormulaWidth + 43)).
```

`specification_successor_step` proves that the emitted opportunity agrees
with the direct formula cursor. The retained coordinate is

```text
formulaVariableSlotBound
+ 1
+ formulaClauseSlotsPerConstraint * formulaTokensPerClause
+ 7.
```

At that coordinate,
`followingTokenSlot_direct_eq_padding_or_t` and
`specification_following_step` prove that the next opportunity is padding
(`none`) at width one and unary `T` at every wider width. The machine
observes and retains this boundary but does not emit it.

## External compiled bound

The raw-transition polynomial evaluates to

```text
BuilderSecondConstraintFirstLiteralTerminatorStep.rawTimeBound(n)
+ 600
+ 24*n
+ 12*FormulaWidth
+ 12*width
+ 12*widthRootPrefixLength
+ 6*widthWorkSteps
+ 6*targetWorkSteps.
```

`rawTimeBound_le` proves this bounds six times the exact work trace. The
compiled interfaces prove exact execution, polynomial-fuel execution,
ordinary-start blank equivalence, acceptance, and non-timeout.

## Fail-closed boundary and audit

The predecessor endpoint is nonhalting before its launch bridge, and
one-step-short total fuel remains timeout. The component tables retain their
audited malformed-workspace behavior, while the combined exact trace,
pairwise query distinction, halt separation, and no-rule-at-accept proofs
prevent bridge removal, shadowing, or state collision from being treated as
success.

The dedicated axiom transcript prints all 80 public declarations in the new
module plus the two strengthened predecessor boundary lemmas. Its measured
approved closure split is 37 empty, 12 `propext`-only, and 33
`propext`/`Quot.sound`; no declaration reaches `Classical.choice` or a
project axiom. The hostile mutation audit rejects altered branch entries,
bridge removal or shadowing, changed output bits, an altered coordinate or
polynomial, swapped successor or following tokens, host-side schedule
lookup, caller certificates, unapproved axioms, and theorem overclaims.

```sh
lake env lean -DwarningAsError=true \
  lean-audit/PNPConcreteCookLevinBuilderSecondConstraintFirstLiteralSuccessorTokenStepAxiomAudit.lean
lake env lean -DwarningAsError=true \
  lean-regression/PNPConcreteCookLevinBuilderSecondConstraintFirstLiteralSuccessorTokenStep.lean
node --test \
  audits/lean-concrete-cook-levin-builder-second-constraint-first-literal-successor-token-step0.test.mjs
```

## Generated publication artifacts

The compiled environment records inventory coordinate
`PNP-LEAN-THEOREM-INVENTORY-2026-07-23-76`: 10,914 declarations, 6,185
theorems, 3,397 assumption-free theorems, 4,240 excluded private declarations,
96 source-closure modules, and 1,689 reviewed milestone candidates. Its
8,774,042 canonical bytes have SHA-256
`037b1bf13da821c60db27d887f32d0f1347072d9288bb21851d7fde525bffbd3`;
the Lean source-closure SHA-256 is
`0822bde5c28639ac3c099e83da02165286ef2dcea6ebab940d7eeb5026b74cee`.

Publication map coordinate `PNP-FORMAL-PUBLICATION-MAP-2026-07-23-76` has 56
milestones, of which 53 are earned and the same three global milestones remain
unearned, plus 1,689 exact kernel-type fingerprints. Its canonical reviewed-
object fingerprint is
`121bbfd89410ac6b1aa0a23bb9bfb0f8687eddd5e4e11b2f23a5500625c079a9`.
Its 532,847 canonical file bytes have SHA-256
`2c58adffea3a4d33ff205433eda9590f4ce5c3f2e6db4764140094aa0534a7dc`.

Status coordinate `PNP-FORMAL-RECONSTRUCTION-STATUS-2026-07-23-76` has
1,323,675 bytes and SHA-256
`19a31a7f64aa1d84478a94d242d302f1a40bdde3507fe56ffaf610ca00094614`.
The generated report coordinate is
`PNP-CANONICAL-FORMAL-RECONSTRUCTION-REPORT-2026-07-23-76`; its 124,295-byte
TeX has SHA-256
`29d22fc03cdfec5b4d73b828aa2c36c718f3b0c71c7dc950fe6b3f22c405c315`,
and its 54-page, 376,670-byte PDF has SHA-256
`3c1edb9f99678ddeeee74da814029cf0ac17a0cdb6cd4b0fbcce1ac5040d7ae3`.

All five activation fingerprints remain unset, all four project assumptions
and six blockers remain, `PNP.Main.p_eq_np` remains absent, and the concrete
publication gate remains false.

## Remaining boundary

This milestone is one fixed width-dependent token transition. It does not
emit the padding or unary token at the retained coordinate, emit the rest of
the second constraint, interpret arbitrary schedule coordinates, implement
a general dynamic formula cursor, emit the remaining formula body, construct
a complete raw formula builder, supply builder `RawRefinement` or a
`PolynomialReduction`, prove CNF-SAT NP-complete or in P, or establish
`PNP.Main.p_eq_np`.
