# Concrete Cook–Levin fourth-clause first-literal prefix

`lean/PNP/Concrete/CookLevinBuilderFourthClauseFirstLiteralPrefix.lean`
composes the complete fourth-clause separator machine with the already audited
three-token `F`, `T`, `F` suffix. Every raw input therefore emits the complete
negative literal on variable one in clause four and retains the coordinate of
the following negative literal sign.

The exact populated output is

```text
T^FormulaWidth F
Sep T F T T F T T T F Finish
Sep F F F T F Finish
Sep F F F T T F Finish
Sep F T F.
```

Rectangular `none` padding between completed clauses is skipped by the
canonical schedule emitter. The following direct token is constructively
proved to be `F`. It is observed by the specification theorem but is not
emitted by this milestone.

## Literal composition

The fixed suffix is reused unchanged from
`BuilderSecondClauseSecondLiteralPrefix.SecondLiteralSuffix.machine`:

```text
selected F appender/cursor: 59 + 9 + 45 = 113 rules
selected T appender/cursor followed by selected F: 113 + 9 + 113 = 235 rules
complete F/T/F suffix: 113 + 9 + 235 = 357 rules.
```

The outer `WorkChain` places that suffix after
`BuilderFourthClauseSeparatorStep.machine` behind one more total nine-symbol
bridge. The complete symbolic rule count is

```text
3666
+ width-evaluator ruleCount
+ body-start-coordinate evaluator ruleCount
+ first-literal-coordinate evaluator ruleCount
+ first-clause-coordinate evaluator ruleCount
+ first-clause-padding evaluator ruleCount
+ second-clause-target evaluator ruleCount
+ second-clause-padding evaluator ruleCount
+ third-clause-target evaluator ruleCount
+ third-clause-padding evaluator ruleCount
+ fourth-clause-target evaluator ruleCount.
```

The constant is the predecessor's `3300`, the outer nine-rule bridge, and the
reused 357-rule suffix. Only the suffix's final cursor supplies global accept
and reject states. The state embeddings are injective, their images are
disjoint, and the combined rule list is pairwise query-distinct, so no bridge
or renamed table can shadow another first-match query.

## Exact trace, output, and schedule

The proof exposes exact runs for all three selected appenders and all three
cursor advances, together with all six launches: predecessor to suffix, each
appender to its cursor, sign cursor to the unary tail, and unary cursor to the
terminator component. `workRunExact` composes them into one exact all-input
trace from the ordinary raw input work tape to the global accepting
configuration.

The independent schedule proof unfolds the first four clauses of the first
shape constraint. It identifies the fourth clause as the excluded pair on
variables one and two and accounts for all three completed rectangular
padding regions. Consequently:

- `fourthClauseFirstLiteralTokens_eq_canonical_formula_prefix` proves the
  finite output is a prefix of `encodeCNFTokens problem.formula`;
- `finalTokenBits_eq_encodedFormula_fourthClauseFirstLiteral` proves exact
  equality with `encodedFormula.take (2 * (FormulaWidth + 31))`;
- `firstLiteralSignSlot_direct_eq_f` proves the negative sign;
- `firstLiteralUnaryUnitSlot_direct_eq_t` proves the unary-one unit;
- `firstLiteralTerminatorSlot_direct_eq_f` proves its terminator; and
- `nextTokenSlot_direct_eq_f` proves the retained next literal sign.

The retained coordinate is

```text
formulaVariableSlotBound + 1 + 3 * formulaTokensPerClause + 4.
```

`finalTape_represents` preserves the raw input, and
`finalOutside_contains_finalTokenSlot` independently audits that coordinate
in the unary workspace.

## External compiled bound

The exact work count consists of the predecessor trace, six bridge steps,
three selected appenders, and three complete bidirectional cursor scans. The
external raw-transition polynomial evaluates to

```text
BuilderFourthClauseSeparatorStep.rawTimeBound(n)
+ 1422
+ 72*n
+ 36*FormulaWidth
+ 36*BuilderFourthClauseSeparatorStep.cursorWord.length.
```

`rawTimeBound_le` proves that polynomial bounds six times the exact work
trace. The compiled interfaces prove exact execution, polynomial-fuel
execution, ordinary-start blank equivalence, acceptance, and non-timeout.

## Fail-closed boundaries and audits

The exact raw-input execution remains `timeout` at all six pre-launch
boundaries: the predecessor endpoint; the sign appender and cursor endpoints;
the unary appender and cursor endpoints; and the terminator appender endpoint.
A malformed tally or output symbol in any appender cannot reach a global halt.
A malformed scratch symbol in any cursor enters the reviewed nonhalting dead
loop. One-step-short total fuel also remains `timeout`.

The regression covers empty input, one-bit zero and one, odd and even lengths,
all-zero and all-one inputs, input-only and paired verifiers, exact rules and
coordinates, all six launches, exact final tape and formula bits, separator
emission, all four direct literal outcomes, polynomial evaluation, compiled
acceptance, and every fail-closed boundary.

```sh
lake env lean -DwarningAsError=true \
  lean-audit/PNPConcreteCookLevinBuilderFourthClauseFirstLiteralPrefixAxiomAudit.lean
lake env lean -DwarningAsError=true \
  lean-regression/PNPConcreteCookLevinBuilderFourthClauseFirstLiteralPrefix.lean
node --test \
  audits/lean-concrete-cook-levin-builder-fourth-clause-first-literal-prefix0.test.mjs
```

The combined kernel audit covers all 97 public declarations in the new module,
16 reviewed interfaces reused from the fixed suffix, and the two cursor
dead-loop facts used for malformed-scratch fail closure. Exactly 33 closures
are empty, 25 use only `propext`, and 57 use only `propext` and `Quot.sound`.
No declaration reaches a project axiom, `Classical.choice`, `sorry`, `admit`,
native/SAT shortcuts, host-side schedule lookup, or a caller-supplied execution
certificate.

## Generated publication artifacts

The compiled environment records inventory coordinate
`PNP-LEAN-THEOREM-INVENTORY-2026-07-21-64`, 9,474 declarations, 5,036
theorems, 3,178 assumption-free theorems, 3,398 excluded private declarations,
84 source-closure modules, and 1,221 reviewed milestone candidates. Its
6,198,052 canonical bytes have SHA-256
`db345c0483274feeb05ed3fd30c973ea8c3dfa06688b2a4b1f3dc5b991ef6406`;
the Lean source-closure SHA-256 is
`102d1806647c18354cbe40744e516d997f03db9a5aeda73af178b8c618cac09c`.

Publication map coordinate `PNP-FORMAL-PUBLICATION-MAP-2026-07-21-64` has
44 milestones, of which 41 are earned and the same three global milestones
are unearned, plus 1,221 exact kernel-type fingerprints. Its 368,941
canonical file bytes have SHA-256
`7f5e3d2a0a65d67fa24a5a0960f8f8e235a53af1cf0ced51846a56e95bd4533a`;
its canonical reviewed-object fingerprint is
`022c475509edbadbbbabda2e65d00365a76044ef0533fa83a922e834e5b28b93`.

Status coordinate `PNP-FORMAL-RECONSTRUCTION-STATUS-2026-07-21-64` has
920,227 bytes and SHA-256
`39a70a771b2a4ac3df1aba9a348d94144db1721c1a18270c85dbe6b7634c9901`.
The generated report coordinate is
`PNP-CANONICAL-FORMAL-RECONSTRUCTION-REPORT-2026-07-21-64`; its 90,040-byte
TeX has SHA-256
`676541e58c89068d7ba3a98b4ee8c0c0d998979c4f8f2eb09ced7e2d8c9b779c`,
and its 40-page, 347,311-byte PDF has SHA-256
`d502b676564e34d7dbc84ca49b90398dbec7d48ee9b54051db2f67e57e7971bf`.
All activation fingerprints remain unset and the publication gate remains
false.

## Remaining boundary

This is one fixed negative literal and three unary cursor advances. It does
not emit the second literal, complete clause four, interpret arbitrary
schedule coordinates, implement a general dynamic formula cursor, emit the
remaining formula body, construct a complete raw formula builder, provide
builder `RawRefinement` or a `PolynomialReduction`, prove CNF-SAT NP-complete
or in P, or establish `PNP.Main.p_eq_np`. The four project assumptions, six
blockers, unset activation fingerprints, and false publication gate remain
unchanged.
