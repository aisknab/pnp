# Cook-Levin post-divider raw route classifier

Status: machine checked in Lean at M214.

M214 closes the next literal boundary after M213's exact divider endpoint. One
fixed 180-rule table copies the exact problem-derived clause count from a
protected workspace sidecar, preserves and restores that sidecar, retains the
complete divider exterior and remainder ledger, and exposes the literal
divider quotient as the coordinate of a shielded M209 comparator.

## Exact M213 tape inputs

`equal_input_tape_is_exact_m213_final` and
`greater_input_tape_is_exact_m213_final` identify the classifier input with
the exact equality and greater-than terminal tapes proved by M213. The result
is not reconstructed semantically on the host: the quotient marks, remainder
ledger, exterior prefix, sidecar count, and arbitrary trailing workspace all
remain on the checked tape.

The public route theorem receives only the verifier tableau problem as its
outer input. It does not accept a route certificate, comparison tape,
precomputed branch, or successful execution trace as proof authority.

## Literal bridge and protected sidecar

`workRunExact` proves the complete trace of the collision-free 180-rule
bridge for every canonical divider terminal geometry, safe exterior prefix,
clause count, and arbitrary workspace. It creates a fresh comparator boundary,
copies the quotient marks into M209's coordinate encoding, copies the exact
clause count from the sidecar, and restores the sidecar before accepting.

`preservedExterior` retains the divider remainder ledger and original
exterior behind the fresh boundary. The bridge therefore does not discard or
reorder the caller's builder workspace while constructing its comparator
input.

## Shielded comparator and route agreement

`shielded_comparator_workRunExact` transports M209's exact raw comparison
trace while proving that the comparator cannot cross the new boundary.
`shieldedComparatorFinal_exterior_preserved` proves byte-for-byte exterior
preservation.

`BranchPhysicalHolds` covers both exact M213 post-header branches.
`DecodedRouteHolds` connects a below-count quotient to the exact M210 body
clause/token coordinates and equality with the clause count to the unique
`Finish` route. `InRangeRouteClassifierHolds` proves that agreement for
every coordinate in the complete current schedule and excludes out-of-range
coordinates without a supplied route witness.

## Compiled execution and bounds

Both the new bridge and the shielded comparator compile with exactly six raw
three-symbol transitions per checked work step. Each exact positive trace is
proved nonhalting one work step before its endpoint.

`workSteps_le_quadratic` bounds the bridge in the complete literal input
geometry. `postDividerWorkSteps_compareResult_le` covers every comparison
branch, and `stagedCompiledSteps_le_rawTimeBound` combines M212/M213 routing,
division, the M214 bridge, and comparison under one verifier-derived polynomial
in the external source-input length. No finite-instance or exhaustive semantic
enumeration supplies the result.

## Proof authority

The axiom transcript prints all 85 public declarations exactly once. Fifty-one
have empty axiom closure, ten use only `propext`, and twenty-four use only
`propext` and `Quot.sound`. No declaration reaches `Classical.choice`, a
project-specific axiom, `sorry`, `admit`, `unsafe`, or
`native_decide`.

## Claim boundary

M214 classifies the physical post-divider route as a body row or the unique
`Finish` row. It does not inspect the selected clause payload, select or emit
a CNF token, append token bits, iterate the schedule, or construct the complete
raw formula.

It therefore does not establish complete builder
`FunctionProgram.RawRefinement`, package the concrete Cook-Levin
`PolynomialReduction`, prove CNFSAT NP-hardness or NP-completeness transport,
put CNFSAT in P, close a global proof gate, create `PNP.Main.p_eq_np`, or
prove P = NP.

Formal artefact coverage increases by one earned publication row to 190 of
192. The fixed-weight proof-completion estimate remains 35 percent, with the
existing 20 to 40 percent uncertainty range. No fixed checkpoint or global
gate changes state.

## Verification surfaces

- Source: `lean/PNP/Concrete/CookLevinBuilderPostDividerRawRouteClassifier.lean`
- Regression: `lean-regression/PNPConcreteCookLevinBuilderPostDividerRawRouteClassifier.lean`
- Axiom audit: `lean-audit/PNPConcreteCookLevinBuilderPostDividerRawRouteClassifierAxiomAudit.lean`
- Hostile audit: `audits/lean-concrete-cook-levin-builder-post-divider-raw-route-classifier0.test.mjs`
- Publication endpoint:
  `PNP.Concrete.CookLevin.BuilderPostDividerRawRouteClassifier.cook_levin_builder_post_divider_raw_route_classifier_checked_complete`
