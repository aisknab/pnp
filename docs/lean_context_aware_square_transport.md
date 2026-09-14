# Context-aware open-support and square transport (M261)

M261 reconstructs the computed Boolean substitution used by the support square
in Sections 2.2 and 3 and the retained-output comparison of Section 11.1,
BN2-CoherentOptimum, of the manuscript pinned by
[`ARCHIVE.json`](../archive/legacy-v0/ARCHIVE.json).

## General construction

The dimensions of the original candidate and the finite terminal record lists
are arbitrary. Ordinary selected-gate inclusion is sufficient; the caller does
not provide a valuation map, correctness certificate or proof oracle.

For a valuation on the larger open boundary, the smaller boundary is computed by
evaluating each of its wires in the larger support. A wire internalized by the
larger support uses its computed gate value, not an independent ambient bit.
Every selected gate and retained interface producer has the same Boolean value
under this substitution. Identity and three-support composition are equalities
of the complete valuation functions.

The theorem covers every larger open-boundary valuation, not only whole-circuit executions.
The actual support-square inclusions derive all four leg maps. Both paths from
join to meet are equal as valuation functions. Retained output values agree for
the extracted circuits, arbitrary valid full realizations, and the actual
canonical full and quotient local-minimum families.

The substitution is derived from the original open carrier. It does not invent
internal gates or charge ownership for a minimum realization. The existing
unconstrained-ambient coherence classifier remains a distinct, unchanged relation.

## Exact reviewed interfaces

| Exact declaration | Checked interface |
| --- | --- |
| `PNP.DirectWire.terminalOpenGateEvaluation_pullback` | Selected gates have identical open values after computed boundary substitution. |
| `PNP.DirectWire.terminalOpenSupportSemantics_pullback` | Every retained interface producer has its larger-support computed value. |
| `PNP.DirectWire.terminalBoundaryPullback_identity` | Transport from a support to itself is the identity valuation function. |
| `PNP.DirectWire.terminalBoundaryPullback_compose` | Nested boundary substitutions compose as complete valuation functions. |
| `PNP.DirectWire.TerminalOptimumLegTransport.selectedGateTransport` | Every actual square leg preserves selected-gate inclusion. |
| `PNP.DirectWire.TerminalFourCornerCarrier.boundaryPullback_meet_join_left` | The left join-to-meet path equals direct computed substitution. |
| `PNP.DirectWire.TerminalFourCornerCarrier.boundaryPullback_meet_join_right` | The right join-to-meet path equals direct computed substitution. |
| `PNP.DirectWire.TerminalFourCornerCarrier.boundaryPullback_square` | The two square paths are equal valuation functions. |
| `PNP.DirectWire.TerminalOptimumLegTransport.extracted_retained_semantics` | Extracted corner circuits agree at retained outputs under the computed map. |
| `PNP.DirectWire.TerminalOptimumLegTransport.realization_retained_semantics` | Arbitrary valid full realizations agree at retained outputs. |
| `PNP.DirectWire.TerminalFourCornerOptimumFamily.full_retained_semantics` | Full local-minimum family realizations agree at retained outputs. |
| `PNP.DirectWire.TerminalFourCornerOptimumFamily.quotient_retained_semantics` | Quotient local-minimum family realizations agree at retained outputs. |
| `PNP.DirectWire.TerminalFourCornerCarrier.canonicalFull_retained_semantics` | The actual canonical full local minima satisfy retained-output transport. |
| `PNP.DirectWire.TerminalFourCornerCarrier.canonicalQuotient_retained_semantics` | The actual canonical quotient local minima satisfy retained-output transport. |

The explicit `PNP` root, exact general theorem types and axiom transcript are
checked by the durable workflow. The reviewed closures use only the standard
`propext` and `Quot.sound` axioms, with no project-specific axiom or
`Classical.choice`. Small bounded executable fixtures exercise empty and equal
supports, repeated and nonconsecutive gate records, retained primary inputs,
internalized wires, both square paths and the independent-ambient distinction.
They do not execute exhaustive canonical minimum searches.

Runtime execution is test evidence, not theorem authority.

## Remaining boundary

Retained Boolean-output transport does not prove arbitrary observer equality or physical minimum gluing.

The theorem covers arbitrary larger open-boundary valuations, not only whole-circuit executions, and introduces no caller-supplied transport or correctness certificate. Retained Boolean-output transport does not prove equality of arbitrary implementation-dependent observers or profiles, physically glue minimum circuits, or establish coherent charge and obligation ownership. Canonical finite reference minima supply specification-level comparison objects, not an efficient executable minimizer. The full manuscript carrier, arbitrary obligation dependency DAGs, complete Package E and global route coverage remain open. This result does not prove unconditional SaturatePositive, BCELReady or ZeroSlack, exact general PCCMin, or total encoded-input-size polynomial runtime, output and certificate bounds for the complete construction. Runtime fixtures are regression evidence, not proof authority. No fixed weighted checkpoint or global gate closes. Deterministic CNFSAT in P and the eligible root remain absent, and P = NP is not proved.

No fixed weighted checkpoint or global proof gate closes. In particular, this is
not a replacement for deriving the complete manuscript carrier and obligation
calculus, coherent charge ownership, every global route, unconditional ZeroSlack
or a complete encoded-input-size polynomial PCCMin construction.

## Progress and publication

Formal artefact coverage: 237 of 239 current scoped publication rows earned.
Risk-weighted proof completion estimate: 40%. Uncertainty range: 20% to 40%. Global gates closed: 0 of 5.

Formal artefact coverage measures the current evidence ledger, not proof
completion. Its denominator may grow. The risk-weighted estimate is neither a
probability that the route is correct nor a time estimate.

Publication decision: defer a separate PNPLabs cycle for M261.
The existing major publication remains bound to its own verified source pin.
See the [milestone plan](plans/2026-09-14-context-aware-square-transport.md),
[canonical progress model](proof_progress.md) and
[formal reconstruction status](FORMAL_RECONSTRUCTION.md).
