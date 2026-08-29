# Arbitrary-slot Cook-Levin header router

`lean/PNP/Concrete/CookLevinBuilderArbitrarySlotHeaderRouter.lean` adds the
M209 first raw decoder layer for the complete Cook-Levin token schedule. One
fixed finite machine accepts exactly when an arbitrary supplied coordinate is
inside the problem-derived formula header and rejects when it is at or beyond
the first body slot.

## Legacy anchor and unbounded abstraction

The manuscript requires one uniform Cook-Levin builder whose behavior is
derived from the verifier and encoded input. M208 supplied an all-input
controller that reaches the complete schedule boundary, but its raw loop did
not interpret individual body coordinates. M209 begins that interpretation at
the first non-repeatable boundary:

```text
arbitrary coordinate < first body slot  -> header coordinate
arbitrary coordinate >= first body slot -> post-header remainder
```

The coordinate may range over every slot below the complete terminal slot. It
is not a named fixed slot, a finite fixture, or a caller-supplied classification
certificate.

## Exact semantic route

`outerRoute` splits a natural coordinate at
`BuilderFullScheduleCursorController.firstBodySlot`. The theorem
`formulaTokenSlotDirect_route` proves that this split is definitionally
faithful to the top-level `DirectSlot.append` used by
`VerifierTableauProblem.formulaTokenSlotDirect`:

- a header coordinate uses `formulaHeaderTokenSlotDirect`;
- a post-header coordinate uses the exact shifted suffix lookup; and
- the less-than and greater-than-or-equal branches have iff characterizations.

No schedule list is materialized to establish this route.

## Literal raw comparator

`RawRouter.machine` is one fixed 54-rule deterministic work machine. Its tape
encodes the arbitrary coordinate and the problem-derived header boundary as
separate unary regions. The machine repeatedly marks one unit from each region
and reaches:

- accept exactly when the coordinate is strictly below the boundary;
- reject exactly when the coordinate equals or exceeds the boundary; or
- an explicit nonhalting dead state for malformed symbols.

The rule table does not depend on the problem, coordinate, boundary, schedule,
or host-language lookup result. `workRunExact` proves the complete trace for
all natural coordinate/boundary pairs, including the less-than, equal, and
greater-than cases. `workBoundedDecide_eq` gives the exact verdict, while
`work_one_step_short_timeout` and `malformed_timeout` make the negative
boundary explicit.

`rawTimeBound` is the verifier-derived polynomial
`36 * terminalSlotPolynomial^2`. Every in-range coordinate runs through the
compiled raw machine within that encoded-input-size bound.

The public earned endpoint is:

```text
PNP.Concrete.CookLevin.BuilderArbitrarySlotHeaderRouter.
  cook_levin_arbitrary_slot_header_router_checked_complete
```

It packages semantic routing, the exact raw trace, the header-branch iff,
the exact accept/reject verdict, compiled execution within the polynomial
bound, the one-step-short timeout, and the fixed 54-rule count.

## Claim boundary

M209 routes only the top-level header boundary. It does not decode the
post-header quotient and remainder into a clause number and within-clause token
slot, and it does not emit a body token. Therefore it does not prove:

- a complete arbitrary-slot raw token decoder;
- the complete raw Cook-Levin formula builder;
- builder `FunctionProgram.RawRefinement`;
- the packaged concrete Cook-Levin `PolynomialReduction`;
- concrete CNFSAT NP-hardness or NP-completeness transport;
- deterministic `CNFSAT in P`; or
- `P = NP`.

Those downstream fields remain false. M209 adds one earned publication row, so
formal artefact coverage is 185 of 187 current scoped rows. No fixed
risk-weighted checkpoint or global gate closes: the
proof-completion estimate remains 35 percent, the uncertainty range remains
20 to 40 percent, and zero of five global gates are closed.

## Verification surfaces

- `lean-audit/PNPConcreteCookLevinBuilderArbitrarySlotHeaderRouterAxiomAudit.lean`
  prints the axiom closure of all 51 public M209 declarations.
- `lean-regression/PNPConcreteCookLevinBuilderArbitrarySlotHeaderRouter.lean`
  checks both input modes, arbitrary and concrete branch cases, the source-size
  bound, compiled trace, exact fuel boundary, and malformed-input timeout.
- `audits/lean-concrete-cook-levin-builder-arbitrary-slot-header-router0.test.mjs`
  rejects boundary shifts, table-size changes, host lookup, missing bounds,
  missing negative cases, shortcuts, and overclaims.

The exact public theorem is pinned in the compiled theorem inventory and formal
publication map.
