# Arbitrary-slot Cook-Levin post-header decoder

`lean/PNP/Concrete/CookLevinBuilderArbitrarySlotPostHeaderDecoder.lean`
adds the M210 all-coordinate semantic decoder immediately after M209's
uniform header router. It decodes every natural post-header coordinate into
the exact clause and within-clause token position, the unique final `Finish`
position, or the out-of-range suffix.

## Unbounded coordinate decoder

`rectangleCoordinate?` is structurally recursive in the problem-derived
clause count. It consumes one fixed-width clause block at a time and returns a
typed pair:

```text
Fin formulaClauseSlotCount x Fin formulaTokensPerClause
```

The coordinate is arbitrary. It is not a fixed slot, finite regression
fixture, or supplied quotient/remainder certificate. The checked
characterization proves that decoding returns `none` exactly at or beyond the
complete rectangle, while `rectangleCoordinate?_reconstruct` proves

```text
clause * formulaTokensPerClause + withinClause = postHeaderCoordinate.
```

## Exact direct-token route

`PostHeaderRoute` distinguishes three cases without materializing the complete
formula schedule:

- `body clauseCoordinate tokenCoordinate` for every rectangular body entry;
- `finish` for the unique coordinate immediately after the body rectangle; and
- `outOfRange` beyond the complete post-header schedule.

`postHeaderSlotDirect_route` proves that interpreting this typed route agrees
exactly with the existing direct post-header lookup. Combined with M209,
`formulaTokenSlotDirect_decoded` gives one semantic decoder for every natural
coordinate: the header branch uses the direct header lookup and the
post-header branch uses the exact clause/token route.

## Checked raw remainder extraction

M209's literal raw comparator already preserves the unmatched coordinate
suffix in its rejecting result configuration. M210 defines a checked reader
for that representation and proves, for every comparison result and every
natural coordinate/boundary pair, that it exposes exactly
`coordinate - boundary` on the post-header branch and nothing on the header
branch. This connects the fixed raw router result to the semantic remainder;
it does not add a host lookup to the raw machine.

The public earned endpoint is:

```text
PNP.Concrete.CookLevin.BuilderArbitrarySlotPostHeaderDecoder.
  cook_levin_arbitrary_slot_post_header_decoder_checked_complete
```

It packages exact direct-token decoding for every in-range schedule
coordinate, exclusion of the out-of-range route, quotient/remainder
reconstruction for every body result, exact extraction from M209's raw result,
and M209's exact raw trace.

## Claim boundary

M210 does not implement raw division, raw body-token emission, or a raw-machine
refinement of the complete semantic decoder. It therefore does not prove:

- the complete raw Cook-Levin formula builder;
- builder `FunctionProgram.RawRefinement`;
- the packaged concrete Cook-Levin `PolynomialReduction`;
- concrete CNFSAT NP-hardness or NP-completeness transport;
- deterministic `CNFSAT in P`;
- any residual-band, ZeroSlack, or PCCMin global gate; or
- `P = NP`.

Those downstream fields remain false. M210 adds one earned publication row, so
formal artefact coverage is 186 of 188 current scoped rows. No fixed
risk-weighted checkpoint or global gate closes: the proof-completion estimate
remains 35 percent, the uncertainty range remains 20 to 40 percent, and zero
of five global gates are closed.

## Verification surfaces

- `lean-audit/PNPConcreteCookLevinBuilderArbitrarySlotPostHeaderDecoderAxiomAudit.lean`
  prints the axiom closure of all 22 public M210 declarations.
- `lean-regression/PNPConcreteCookLevinBuilderArbitrarySlotPostHeaderDecoder.lean`
  checks arbitrary rectangle coordinates, exact boundaries, both verifier input
  modes, direct token routing, raw remainder extraction, and the public endpoint.
- `audits/lean-concrete-cook-levin-builder-arbitrary-slot-post-header-decoder0.test.mjs`
  rejects decoder-boundary shifts, lost reconstruction, host-token substitution,
  shifted raw remainders, missing endpoints, shortcuts, and overclaims.

The exact public theorem is pinned in the compiled theorem inventory and formal
publication map.
