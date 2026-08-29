# Full-schedule Cook-Levin cursor controller

`lean/PNP/Concrete/CookLevinBuilderFullScheduleCursorController.lean` adds the
M208 all-input control layer for the remaining Cook-Levin formula schedule. It
replaces continued fixed-slot extension as the control architecture. The
module computes the complete body-opportunity count from the verifier and raw
input, consumes that arbitrary count with one literal finite countdown table,
and materializes the exact terminal token coordinate.

## Legacy anchor and unbounded abstraction

The legacy manuscript describes a uniform Cook-Levin construction whose
formula depends on the verifier and input. Earlier literal builder milestones
machine-checked useful prefixes, but their control path advanced through named
fixed opportunities. M208 introduces a single input-dependent abstraction:

```text
first body coordinate
  + (clause count * fixed clause-token width + final Finish)
  = complete token-schedule length
```

The count is a `NatPolynomial` derived from the concrete verifier. It is not a
caller-supplied schedule length, cursor, token list, or trace certificate.

## Exact semantic traversal

`TokenCursor.run` iterates the existing direct token cursor with arbitrary
fuel. The proved prefix, terminal, and excess-fuel laws establish that:

- the full run returns exactly `problem.formulaTokenSchedule`;
- the body run starts immediately after the padded unary header and stops at
  `problem.formulaTokenSlotCountDirect`;
- emitting the returned entries yields exactly `encodeCNFTokens
  problem.formula`;
- surplus fuel does not invent additional entries after the terminal cursor.

## Literal raw controller

The raw controller composes four existing finite components:

1. `BuilderCompleteHeader.machine`;
2. a unary evaluator for the complete body-opportunity count;
3. the 25-rule positive countdown table; and
4. a unary evaluator for the exact terminal schedule coordinate.

Three fixed nine-rule launch bridges connect those components. The combined
rule table is finite and pairwise query-distinct. No rule is sourced at the
global accept state, and accept and reject states remain distinct.

For every raw input, `workRunExact` proves the complete composed trace. The
final tape still represents the original input, retains the exact header token
output, and contains the computed terminal coordinate. `rawTimeBound` is an
explicit natural polynomial covering the complete-header machine, both unary
evaluators, all three bridges, and the entire input-dependent countdown. The
compiled machine accepts within that bound.

The negative boundary is explicit. A malformed scratch symbol or malformed
countdown root stays at timeout. The complete header endpoint is still timeout
before the outer launch, and the exact composed trace is timeout one work step
short.

The public earned endpoint is:

```text
PNP.Concrete.CookLevin.BuilderFullScheduleCursorController.
  cook_levin_full_schedule_cursor_controller_checked_complete
```

It packages the complete semantic run, exact raw trace, terminal-coordinate
identity, polynomial bound, compiled acceptance, and both timing boundaries.

## Claim boundary

The countdown is a control scaffold. It consumes one unit per body
opportunity, but it does not yet decode the entry at each visited coordinate or
append the corresponding raw token. Therefore M208 does not prove:

- a general raw dynamic slot decoder;
- the complete raw Cook-Levin formula builder;
- builder `FunctionProgram.RawRefinement`;
- the packaged concrete Cook-Levin `PolynomialReduction`;
- concrete CNFSAT NP-hardness or NP-completeness transport;
- deterministic `CNFSAT in P`; or
- `P = NP`.

The status fields for those downstream obligations remain false. This
milestone adds one earned formal publication row, so formal artefact coverage
is 184 of 186 current scoped rows. No fixed risk-weighted checkpoint or global
gate closes: the proof-completion estimate remains 35 percent, the uncertainty
range remains 20 to 40 percent, and zero of five global gates are closed.

## Verification surfaces

- `lean-audit/PNPConcreteCookLevinBuilderFullScheduleCursorControllerAxiomAudit.lean`
  prints the axiom closure of every public M208 declaration.
- `lean-regression/PNPConcreteCookLevinBuilderFullScheduleCursorController.lean`
  checks both input modes and the load-bearing semantic, raw, polynomial, and
  fail-closed interfaces.
- `audits/lean-concrete-cook-levin-builder-full-schedule-cursor-controller0.test.mjs`
  rejects fixed-count, host-lookup, missing-bridge, missing-boundary, and
  overclaim mutations.

The exact public theorem is also pinned in the compiled theorem inventory and
formal publication map.
