# Cook-Levin post-header raw tape bridge

Status: machine checked in Lean at M213.

M213 replaces M212's value-level launch with a literal finite-machine handoff.
The literal tape bridge is one fixed 351-rule table that consumes the exact
equality and greater-than terminal
tapes produced by M209, derives the shifted remainder from their branch and
tape layout, copies the problem-derived clause width, and reaches a shielded
M211 divider input while preserving arbitrary exterior builder workspace.

## Exact router-tape inputs

`equalInputTape_is_exact_router_result` and
`greaterInputTape_is_exact_router_result` identify the bridge inputs with the
corresponding M209 result tapes, extended only by the positive unary width, a
fresh divider shield, and the caller's arbitrary workspace. Distinct entry
states preserve whether M209 found equality or a strict post-header remainder.

The bridge does not accept a supplied remainder, quotient, route certificate,
or execution trace. Its equality branch constructs zero remainder. Its greater
branch copies the exact `remainingCoordinate + 1` unary units already present
on M209's tape.

## Literal bridge and shielded divider traces

`equal_workRunExact` and `greater_workRunExact` prove the complete bridge
traces for every positive width and arbitrary workspace. Zero width enters the
nonhalting dead state on both entries. The 351-rule table is pairwise
collision-free and its accept and reject states are distinct.

The bridge marks copied remainder and width cells, constructs M211's canonical
divider word behind a fresh left boundary, and restores the head to the exact
divider start. The original router cells and arbitrary exterior workspace are
retained beyond that boundary.

`shielded_divider_workRunExact` transports M211's exact trace without reading,
writing, or crossing the preserved exterior. The final head and right tape are
the canonical M211 result, the left tape is that result followed byte-for-byte
by the exterior, and `shielded_final_quotient_remainder` recovers exactly
`(dividend / width, dividend % width)` after stripping the exterior.

## Compiled execution and bounds

The equality, greater, and shielded-divider traces compile with exactly six raw
three-symbol transitions per checked work step. Each positive-width trace is
proved nonhalting one step before its exact endpoint.

The bridge has explicit quadratic bounds for both branches. The public
`stagedCompiledSteps_le_rawTimeBound` theorem combines M209 routing, the literal
bridge, and shielded M211 division under one verifier-derived polynomial in the
external source-input length for every coordinate inside the complete token
schedule. It performs no subset, support, payload, implementation, or semantic
reference enumeration.

## All-coordinate endpoint

`ResultBridgeHolds` covers the header, equality, and strict-greater comparison
results without supplied branch data. `InRangeRouteBridgeHolds` binds those
physical traces back to M210's header, body, and `Finish` routes and excludes
the out-of-range post-header branch for every finite in-range coordinate.

The public endpoint quantifies over every verifier tableau problem, arbitrary
workspace, and in-range coordinate. It retains the collision-free table, exact
bridge/divider evidence, and source-size polynomial bound in one theorem.

## Proof authority

The axiom transcript prints all 78 public declarations exactly once. Fifty-seven
have empty axiom closure, two use only `propext`, and nineteen use only
`propext` and `Quot.sound`. No declaration reaches `Classical.choice`, a
project-specific axiom, `sorry`, `admit`, `unsafe`, or `native_decide`.

## Claim boundary

M213 ends with the exact quotient and remainder on a literal tape with the
complete exterior preserved. It does not select, emit, or append the
corresponding body or `Finish` token, iterate this subroutine through the full
schedule, or construct the complete raw formula.

It therefore does not establish complete builder `FunctionProgram.RawRefinement`,
package the concrete Cook-Levin `PolynomialReduction`, prove CNFSAT
NP-hardness or NP-completeness transport, put CNFSAT in P, close a global proof
gate, create `PNP.Main.p_eq_np`, or prove P = NP.

Formal artefact coverage increases by one earned publication row to 189 of
191. The fixed-weight proof-completion estimate remains 35 percent, with the
existing 20 to 40 percent uncertainty range. No fixed checkpoint or global
gate changes state.

## Verification surfaces

- Source: `lean/PNP/Concrete/CookLevinBuilderPostHeaderRawTapeBridge.lean`
- Regression: `lean-regression/PNPConcreteCookLevinBuilderPostHeaderRawTapeBridge.lean`
- Axiom audit: `lean-audit/PNPConcreteCookLevinBuilderPostHeaderRawTapeBridgeAxiomAudit.lean`
- Hostile audit: `audits/lean-concrete-cook-levin-builder-post-header-raw-tape-bridge0.test.mjs`
- Publication endpoint:
  `PNP.Concrete.CookLevin.BuilderPostHeaderRawTapeBridge.cook_levin_builder_post_header_raw_tape_bridge_checked_complete`
