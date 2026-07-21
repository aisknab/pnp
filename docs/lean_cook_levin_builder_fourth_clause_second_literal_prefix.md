# Concrete Cook–Levin fourth-clause second-literal prefix

`lean/PNP/Concrete/CookLevinBuilderFourthClauseSecondLiteralPrefix.lean`
composes the complete fourth-clause first-literal machine with the already
audited four-token `F`, `T`, `T`, `F` suffix. Every raw input therefore emits
the complete negative literal on variable two in clause four and retains the
coordinate of the following clause terminator.

The exact populated output is

```text
T^FormulaWidth F
Sep T F T T F T T T F Finish
Sep F F F T F Finish
Sep F F F T T F Finish
Sep F T F F T T F.
```

Rectangular `none` padding between completed clauses is skipped by the
canonical schedule emitter. The following direct token is constructively
proved to be `Finish`. The machine does not emit that following `Finish`.

## Literal composition

The fixed suffix is reused unchanged from
`BuilderThirdClauseSecondLiteralPrefix.SecondLiteralSuffix.machine`:

```text
selected F appender/cursor: 59 + 9 + 45 = 113 rules
selected T appender/cursor followed by selected F: 113 + 9 + 113 = 235 rules
selected T followed by the T/F tail: 113 + 9 + 235 = 357 rules
complete F/T/T/F suffix: 113 + 9 + 357 = 479 rules.
```

The outer `WorkChain` places that suffix after
`BuilderFourthClauseFirstLiteralPrefix.machine` behind one more total
nine-symbol bridge. The complete symbolic rule count is

```text
4154
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

The constant is the predecessor's `3666`, the outer nine-rule bridge, and the
reused 479-rule suffix. Only the suffix's final cursor supplies global accept
and reject states. The state embeddings are injective, their images are
disjoint, and the combined rule list is pairwise query-distinct, so no bridge
or renamed table can shadow another first-match query.

## Exact trace, output, and schedule

The proof exposes exact runs for all four selected appenders and all four
cursor advances, together with all eight launches: predecessor to suffix,
each appender to its cursor, and each of the three internal suffix bridges.
`workRunExact` composes them into one exact all-input trace from the ordinary
raw-input work tape to the global accepting configuration.

The independent schedule proof unfolds the first four clauses of the first
shape constraint. It identifies the fourth clause as the excluded pair on
variables one and two and accounts for all three completed rectangular
padding regions. Consequently:

- `fourthClauseSecondLiteralTokens_eq_canonical_formula_prefix` proves the
  finite output is a prefix of `encodeCNFTokens problem.formula`;
- `finalTokenBits_eq_encodedFormula_fourthClauseSecondLiteral` proves exact
  equality with `encodedFormula.take (2 * (FormulaWidth + 35))`;
- the four direct-slot theorems prove the second literal is exactly
  `F T T F`; and
- `nextTokenSlot_direct_eq_finish` proves the retained next coordinate
  contains `Finish`.

The retained coordinate is

```text
formulaVariableSlotBound + 1 + 3 * formulaTokensPerClause + 8.
```

`finalTape_represents` preserves the raw input, and
`finalOutside_contains_finalTokenSlot` independently audits that coordinate
in the unary workspace.

## External compiled bound

The exact work count consists of the predecessor trace, eight bridge steps,
four selected appenders, and four complete bidirectional cursor scans. The
external raw-transition polynomial evaluates to

```text
BuilderFourthClauseFirstLiteralPrefix.rawTimeBound(n)
+ 2232
+ 96*n
+ 48*FormulaWidth
+ 48*BuilderFourthClauseSeparatorStep.cursorWord.length.
```

`rawTimeBound_le` proves that polynomial bounds six times the exact work
trace. The compiled interfaces prove exact execution, polynomial-fuel
execution, ordinary-start blank equivalence, acceptance, and non-timeout.

## Fail-closed boundaries and audits

The exact raw-input execution remains `timeout` at all eight pre-launch
boundaries: the predecessor endpoint; all four appender endpoints; and the
first three cursor endpoints. A malformed tally or output symbol in any
appender cannot reach a global halt. A malformed scratch symbol in any cursor
enters the reviewed nonhalting dead loop. One-step-short total fuel also
remains `timeout`.

The regression covers empty input, one-bit zero and one, odd and even lengths,
all-zero and all-one inputs, input-only and paired verifiers, exact rules and
coordinates, all eight launches, exact final tape and formula bits, the
complete negative literal on variable two, all five direct schedule outcomes,
polynomial evaluation, compiled acceptance, and every fail-closed boundary.

```sh
lake env lean -DwarningAsError=true \
  lean-audit/PNPConcreteCookLevinBuilderFourthClauseSecondLiteralPrefixAxiomAudit.lean
lake env lean -DwarningAsError=true \
  lean-regression/PNPConcreteCookLevinBuilderFourthClauseSecondLiteralPrefix.lean
node --test \
  audits/lean-concrete-cook-levin-builder-fourth-clause-second-literal-prefix0.test.mjs
```

The combined kernel audit covers all 124 public declarations in the new
module, 21 reviewed interfaces reused from the fixed suffix, and the two
cursor dead-loop facts used for malformed-scratch fail closure. Exactly 46
closures are empty, 32 use only `propext`, and 69 use only `propext` and
`Quot.sound`. No declaration reaches a project axiom, `Classical.choice`,
`sorry`, `admit`, native/SAT shortcuts, host-side schedule lookup, or a
caller-supplied execution certificate.

## Generated publication artifacts

The compiled environment records inventory coordinate
`PNP-LEAN-THEOREM-INVENTORY-2026-07-21-65`, 9,661 declarations, 5,173
theorems, 3,215 assumption-free theorems, 3,509 excluded private declarations,
85 source-closure modules, and 1,295 reviewed milestone candidates. Its
6,615,591 canonical bytes have SHA-256
`84ba24b2779664619022bc89cacedbd030f3a1cbfebe944ad2ed81351c7191c5`;
the Lean source-closure SHA-256 is
`78a490d5d59cea47182bafb1875a24f1c2cd9d51ac1902cf108278d4c4373692`.

Publication map coordinate `PNP-FORMAL-PUBLICATION-MAP-2026-07-21-65` has
45 milestones, of which 42 are earned and the same three global milestones
are unearned, plus 1,295 exact kernel-type fingerprints. Its 393,933 canonical
file bytes have SHA-256
`491a24cbc52491f7faeded5cb7c28d99fe1716ac637e134685f6897f508059f7`;
its canonical reviewed-object fingerprint is
`f0d16995109272e11530223aa08a3f6cd9b3daaf3c6f08dd9d7d2b0ecad5c310`.

Status coordinate `PNP-FORMAL-RECONSTRUCTION-STATUS-2026-07-21-65` has
984,156 bytes and SHA-256
`7822370f79876d4c62b4f70a624bfc43efd9dc0f2bd0dafc5e8d1e1032882666`.
The generated report coordinate is
`PNP-CANONICAL-FORMAL-RECONSTRUCTION-REPORT-2026-07-21-65`; its 93,070-byte
TeX has SHA-256
`b0befcc14f61ca42179362b7e369b0611f7a5084a575ba788ce95a860403d0d7`,
and its 41-page, 348,387-byte PDF has SHA-256
`09ffb5a9569b3fc42d6ab84e69717b819f3a415b8f029b3de1c3a9fb24eee035`.
All activation fingerprints remain unset and the publication gate remains
false.

## Remaining boundary

This is one fixed negative literal and four unary cursor advances. It does
not emit the following `Finish`, complete clause four, interpret arbitrary
schedule coordinates, implement a general dynamic formula cursor, emit the
remaining formula body, construct a complete raw formula builder, provide
builder `RawRefinement` or a `PolynomialReduction`, prove CNF-SAT NP-complete
or in P, or establish `PNP.Main.p_eq_np`. The four project assumptions, six
blockers, unset activation fingerprints, and false publication gate remain
unchanged.
