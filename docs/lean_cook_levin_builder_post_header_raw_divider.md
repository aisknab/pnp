# Cook-Levin post-header raw divider

Status: machine checked in Lean at M211.

M211 adds a standalone raw arithmetic kernel for the post-header rectangle
coordinates isolated by M209 and interpreted semantically by M210. One fixed
deterministic work machine performs unary quotient/remainder division for every
natural dividend and every positive unary width.

The milestone is intentionally narrower than a complete raw Cook-Levin decoder.
It proves the arithmetic kernel independently before the later composition that
must launch it from the checked outer-route result and emit the selected token.

## Fixed machine

`PNP.Concrete.CookLevin.BuilderPostHeaderRawDivider.rules` is one literal table
of 99 rules. The audited interface proves:

- the exact rule count;
- pairwise query distinctness;
- separated accept and reject states;
- no rule sourced from the accept state; and
- deterministic fail-closed behavior for malformed work configurations.

The work alphabet reuses the concrete two-track symbols already compiled by the
finite-machine kernel. Dedicated marks distinguish matched dividend and divisor
units, consumed dividend units, quotient units, the separator, end marker and
left boundary.

## Exact all-input trace

For a dividend `d` and positive width `w`, the start tape contains the unary
dividend and divisor. Each complete pass consumes exactly `w` dividend units,
restores the divisor and appends one quotient mark. The terminal partial pass
restores the strict remainder and accepts.

The public theorem
`BuilderPostHeaderRawDivider.workRunExact` proves, for every `d` and positive
`w`, that the exact `workSteps d w` execution reaches
`finalConfiguration d w`. This is not a finite fixture or a supplied execution
certificate: the proof is uniform in both natural inputs.

The dispatcher `divide?` returns `none` at width zero, so the public division
claim never relies on an undefined zero-width quotient interpretation.

## Quotient and remainder

The terminal decoder counts quotient marks and removes the preserved divisor
prefix from the remaining unary units. The checked result is exactly

```text
(d / w, d % w)
```

for every natural `d` and positive `w`. Separate theorems prove

```text
(d / w) * w + d % w = d
d % w < w
```

so the accepted tape carries both exact reconstruction and the strict-remainder
condition.

M210's semantic body route supplies a finite clause coordinate and a finite
within-clause coordinate. M211 proves that instantiating the divider with that
post-header index and `formulaTokensPerClause` decodes exactly those two natural
coordinates, while preserving the full exact work trace.

## Raw compilation and bound

`run_compile_exact` transports every certified work transition through the
existing work-machine compiler. The compiled raw machine takes exactly six raw
transitions per work step and reaches the encoded terminal configuration.

The checked external bound is

```text
workSteps d w <= 20 * (d + w + 1) * (d + w + 1).
```

This is a quadratic bound in the complete unary encoded input length. The
construction does not enumerate subsets, supports, payloads, candidate
implementations or semantic reference minima. A separate theorem proves that
one step less than the exact work budget returns timeout.

## Proof authority

The axiom transcript prints every one of the 55 public declarations exactly
once. The current closure distribution is:

- 31 declarations with empty axiom closure;
- 3 declarations using only `propext`; and
- 21 declarations using only `propext` and `Quot.sound`.

No declaration reaches `Classical.choice`, a project-specific axiom, `sorry`,
`admit`, `unsafe` or `native_decide`.

## Claim boundary

M211 does not splice this divider onto M209's checked raw result tape. It does
not classify the M210 `Finish` or out-of-range branches inside a raw machine,
emit or append the selected body token, construct the complete raw formula, or
prove `FunctionProgram.RawRefinement` for a complete builder.

It therefore does not package the concrete Cook-Levin `PolynomialReduction`,
establish CNFSAT NP-hardness or NP-completeness transport, put CNFSAT in P,
close a global proof gate, create `PNP.Main.p_eq_np`, or prove P = NP.

Formal artefact coverage increases by one earned publication row to 187 of 189.
The fixed-weight proof-completion estimate remains 35 percent, with the existing
20 to 40 percent uncertainty range. No fixed checkpoint or global gate changes
state.

## Verification surfaces

- Source: `lean/PNP/Concrete/CookLevinBuilderPostHeaderRawDivider.lean`
- Regression: `lean-regression/PNPConcreteCookLevinBuilderPostHeaderRawDivider.lean`
- Axiom audit: `lean-audit/PNPConcreteCookLevinBuilderPostHeaderRawDividerAxiomAudit.lean`
- Hostile audit: `audits/lean-concrete-cook-levin-builder-post-header-raw-divider0.test.mjs`
- Publication endpoint:
  `PNP.Concrete.CookLevin.BuilderPostHeaderRawDivider.cook_levin_builder_post_header_raw_divider_checked_complete`
