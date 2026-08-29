# Cook-Levin arbitrary-slot header-router milestone

## Legacy anchor

The pinned manuscript's final complexity step uses the standard fact that SAT
is NP-complete. The active reconstruction must supply that transport in the
selected concrete machine model, so the Cook-Levin construction must be a
uniform polynomial-time raw builder rather than a host-side formula lookup.

M208 introduced an all-input controller for the complete generated token
schedule. Its canonical plan names the next load-bearing dependency as a raw
arbitrary-slot decoder tied to `formulaTokenSlotDirect`. That decoder has a
finite outer decomposition: padded header, clause-token body, final `Finish`,
and out-of-range. M209 closes the first outer boundary rather than returning to
fixed schedule prefixes.

## Unbounded abstraction

The theorem ranges over every `PolynomialTimeVerifier`, every raw input, both
tableau input modes, and every natural token coordinate within the complete
input-dependent schedule. No constraint, clause, literal, token coordinate,
input length, tableau width, decoded token, route outcome, or success
certificate is fixed or supplied as proof authority.

The literal arithmetic component ranges over arbitrary unary coordinate and
boundary values. Its finite rule table contains neither value. For canonical
register geometry it must accept exactly when the coordinate is strictly
below the boundary and reject exactly when it is at or above the boundary.

## Exact theorem boundary

Add `PNP.Concrete.CookLevin.BuilderArbitrarySlotHeaderRouter` with:

1. an outer semantic route that classifies an arbitrary coordinate as header
   or post-header and retains the exact post-header remainder;
2. exact equations reducing `formulaTokenSlotDirect` to
   `formulaHeaderTokenSlotDirect` below the first-body coordinate and to the
   existing body-plus-`Finish` direct lookup at or above it;
3. one fixed literal work machine that compares two delimiter-separated unary
   values without consulting `NatPolynomial.eval`, `formulaTokenSchedule`,
   `formulaTokenSlotDirect`, a host-side comparison, or an input-dependent rule
   table;
4. exact all-value work traces for both strict-less and greater-or-equal
   branches, pairwise query-distinct rules, distinct halts, and preserved
   canonical tape geometry;
5. a compiled exact-run theorem and an explicit input-size polynomial bound
   for every coordinate inside the generated schedule; and
6. fail-closed malformed-symbol and one-step-short boundaries.

The public endpoint is
`cook_levin_arbitrary_slot_header_router_checked_complete`.

## Downstream blockers

M209 decides only the unique top-level header boundary. It does not decode the
header token itself, divide a body coordinate into clause and in-clause
coordinates, derive the selected local constraint or clause, decode a literal
token, append a decoded body token, integrate the decoder into the M208 loop,
feed the final odd zero bit, construct the complete formula builder, provide
builder `FunctionProgram.RawRefinement`, or package the concrete
`PolynomialReduction`.

Concrete CNF-SAT NP-hardness and NP-completeness, deterministic `CNFSAT in P`,
the residual-band minimizer, unconditional ZeroSlack, polynomial PCCMin, the
eligible root theorem, and the publication gate remain open.

## Conservative progress decision

This is an unbounded raw construction dependency, but it does not close the
fixed complete-builder checkpoint or a global proof gate. The risk-weighted
proof-completion estimate therefore remains 35 percent with the 20 to 40
percent uncertainty range. Formal artefact coverage will be regenerated from
the authoritative publication ledger after the new row and its remaining
global obligation are reconciled.

## Regression and hostile evidence

- Compile the semantic outer-route equations, both arbitrary-value raw trace
  branches, the in-range polynomial bound, compiled execution, and fail-closed
  boundaries.
- Exercise zero, equality, strict-less, and strict-greater comparisons and
  coordinates on both sides of the input-dependent header boundary in both
  tableau input modes.
- Derive the axiom transcript from every public declaration in the module.
- Reject fixed coordinates, value-dependent rules, host-side comparisons in
  executable actions, direct schedule lookup in the machine, a missing equality
  case, timeout-as-rejection, malformed acceptance, a missing polynomial bound,
  or documentation that calls the outer router a complete slot decoder or
  formula builder.

## Release gates

Run the focused Lean regression and axiom audit first, followed by the focused
hostile audit. Reconcile the compiled inventory, publication map, formal status,
canonical report, proof-progress ledger, workflow, and current documentation.
Run one complete capped remote verification, publish a focused draft PR,
require every normal check, merge manually, and reproduce the exact merge from
a fresh clean remote-builder checkout. Synchronize that exact core merge into
PNPLabs, perform the required full publication-surface audit without recompiling Lean,
merge and reproduce the exact site commit, deploy it through the narrow
deployer, and independently verify production provenance and bytes.
