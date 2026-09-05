# Lean Cook-Levin all-route physical body-remainder split

M229 closes the physical remainder-read dependency after M228. Its legacy
anchor is the manuscript’s `TraceEquivalence` requirement for a uniform
concrete Cook-Levin formula builder.

## Construction and exact boundary

One fixed 895-rule graph runs M228 and preserves its completed `Finish`
endpoint. Every body route instead enters a fixed 36-rule scanner. The scanner
crosses the actual clause-count and exterior boundaries, skips consumed
dividend marks, and reads the retained remainder: a separator means zero and
a unit means positive. The remainder is proved equal to the canonical body
token coordinate. The graph’s two body outcomes both remain rejecting
continuation boundaries, distinguished by their terminal tape contents.

The canonical builder word and retained ledger are preserved as the head
moves across them. No route, remainder, request, trace, or correctness
certificate is supplied on the input tape. The component starts from the
canonical entry configuration derived from the verifier problem and schedule
coordinate; constructing and connecting successive entries remains open.

The endpoint takes only a `VerifierTableauProblem` and quantifies internally
over every coordinate in the complete post-header schedule:

```lean
PNP.Concrete.CookLevin.BuilderPhysicalClassifierAllRouteBodyRemainderSplit.cook_levin_builder_physical_classifier_all_route_body_remainder_split_checked_complete
```

Lean proves exact work-machine execution, six-for-one compiled execution,
nonhalting one work step before completion, the route-specific terminal
contract, and a polynomial bound in the encoded verifier input length.
The added scan is linear in the existing verifier-derived size measure.

All 71 public declarations are audited: 39 have empty axiom closure, nine use
only `propext`, and 23 use only `propext` and `Quot.sound`. There is no
`Classical.choice` or project-specific axiom in these closures.

## Remaining obligations

M229 preserves Finish and physically distinguishes zero from positive body remainder using the retained divider ledger, but clause occupancy, body-token and padding request synthesis, successive-coordinate composition, the repeated builder loop, builder RawRefinement and the packaged PolynomialReduction remain open.

Formal artefact coverage is 205 of 207 current scoped publication rows earned. The risk-weighted proof completion estimate remains 35 percent, with an uncertainty range of 20 to 40 percent. Global gates closed: 0 of 5.

The full Cook-Levin builder checkpoint remains open. M229 does not establish
concrete NP-hardness transport, `CNFSAT ∈ P`, a global proof gate, the eligible
root theorem, or `P = NP`.

## Verification

- [Lean source](../lean/PNP/Concrete/CookLevinBuilderPhysicalClassifierAllRouteBodyRemainderSplit.lean)
- [Complete axiom audit](../lean-audit/PNPConcreteCookLevinBuilderPhysicalClassifierAllRouteBodyRemainderSplitAxiomAudit.lean)
- [Kernel regression fixtures](../lean-regression/PNPConcreteCookLevinBuilderPhysicalClassifierAllRouteBodyRemainderSplit.lean)
- [Source and publication contracts](../audits/lean-concrete-cook-levin-builder-physical-classifier-all-route-body-remainder-split0.test.mjs)
- [Milestone plan](plans/2026-09-05-cook-levin-all-route-physical-body-remainder-split.md)
- [Progress ledger](../status/PROOF_PROGRESS.json)
