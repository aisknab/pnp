# Computed dead-support frames and proper physical deletion

M245 closes the physical unused-gate replacement edge behind the manuscript's
section 5 Package E and Traceable normalization boundary. It builds on M244's
[computed output cone](lean_pccmin_output_cone_pruning.md) and the existing
[conditional final-report bridge](lean_concrete_final_report_bridge.md).
The pinned manuscript remains a specification, not Lean proof authority.

M245 computes a proper physical deletion component from the actual unused-gate complement. The live frontier supplies the support inputs and all original outputs as bypass; the actual extracted support is reindexed only by its proved empty outgoing interface. A concrete replacement frame preserves complete output semantics and accounts for every removed gate and unit of residual slack. The gain witness accepts only a nonempty dead support with a nonempty retained cone. This is not complete manuscript Package E admissibility, full-profile normalization or global PCCMin.

Formal artefact coverage: 221 of 223 current scoped publication rows earned.
Risk-weighted proof completion estimate: 40%. Uncertainty range: 20% to 40%. Global gates closed: 0 of 5.

## Computed construction

1. Compute the physical complement of the complete output cone.
2. Prove that no selected dead gate feeds a live gate or original output, so
   its actual outgoing interface is empty.
3. Reuse the live frontier to compute every incoming support wire; original
   ordered outputs are carried as bypass, including constants, inputs and repeats.
4. Reindex the actual extracted support by the proved empty interface. Its
   physical program is unchanged; outputs are not discarded by an assumption.
5. Construct the concrete environment/support/continuation frame. Reinserted
   support has exactly the original physical gate count and output semantics.
6. Plug an empty zero-gate support. Prove complete output equivalence, exact
   retained-plus-dead accounting and exact residual-slack savings.
7. Return a physical gain witness exactly when both dead support and live cone
   contain a gate.

No support, frame or correctness certificate is supplied by the caller.
The frontier wrapper exposes the existing checked computation, not a second
compiler. The dead complement need not be predecessor-closed; it is therefore
not passed to a saturation-context theorem that requires that stronger condition.

## Twenty reviewed general interfaces

The first theorem is in
[`PCCMinOutputConePruning.lean`](../lean/PNP/PCCMinOutputConePruning.lean);
the remaining interfaces are in
[`PCCMinDeadSupportContext.lean`](../lean/PNP/PCCMinDeadSupportContext.lean).

- `PNP.DirectWire.outputConeFrontierCandidate_semantics`
- `PNP.DirectWire.deadSupport_interface_empty`
- `PNP.DirectWire.deadSupportGateCount_partition`
- `PNP.DirectWire.deadSupportGateCount_eq_deleted`
- `PNP.DirectWire.deadSupportEnvironment_boundary`
- `PNP.DirectWire.deadSupportEnvironment_bypass`
- `PNP.DirectWire.deadSupportCandidate_extracted`
- `PNP.DirectWire.deadSupportCandidate_program`
- `PNP.DirectWire.deadSupportEmptyReplacement_equivalent`
- `PNP.DirectWire.deadSupportContext_plug_equivalent`
- `PNP.DirectWire.deadSupportContext_original_size`
- `PNP.DirectWire.deadSupportReplacement_gateCount`
- `PNP.DirectWire.deadSupportReplacement_equivalent`
- `PNP.DirectWire.deadSupportReplacement_accounting`
- `PNP.DirectWire.deadSupportReplacement_residualSlack`
- `PNP.DirectWire.deadSupportReplacement_strictGain_iff`
- `PNP.DirectWire.deadSupportProperGain_isSome_iff`
- `PNP.DirectWire.deadSupportProperGain_sound`
- `PNP.DirectWire.deadSupportProperGain_none_of_all_dead`
- `PNP.DirectWire.deadSupportProperGain_none_of_no_dead`

The [explicit-root axiom audit](../lean-audit/PNPDeadSupportContextAxiomAudit.lean)
checks exactly these interfaces. Their dependencies are only `propext` and
`Quot.sound`, with no project-specific axiom or `Classical.choice`.
The canonical inventory and publication map retain exact kernel-type fingerprints.

## Claim boundary

This is a computed proper physical deletion component, not complete manuscript
Package E admissibility or a complete N1-N10 normalization ledger. Properness is
about the physical gate subset and concrete frame, not full-profile carrier,
rank, obligation or metadata compatibility.

An all-unused circuit is not accepted as a proper-subset witness. An empty
dead support is also rejected. Rejecting this route does not imply semantic
minimality or ZeroSlack: an all-live circuit can still have a smaller equivalent
implementation. Arbitrary full-profile observers can distinguish a changed
physical gate count.

The construction does not execute a reference-minimum search; the minimum
appears only in specification theorems about exact slack savings. Finite
termination is not a uniformly encoded-size polynomial execution theorem.
No full-profile Package E verifier, complete normalization ledger, global
terminal-derived family, complete rank-decreasing route coverage, total PCCMin
oracle, unconditional SaturatePositive/BCELReady/ZeroSlack, deterministic SAT
or eligible root theorem is established.

## Validation and publication

[General type and bounded executable regressions](../lean-regression/PNPDeadSupportContext.lean)
exercise interleaved live/dead gates, live producers used by dead gates, all
ordered outputs, empty and all-unused circuits, zero-input constants and the
properness/profile/minimality distinctions.
Runtime execution is test evidence, not theorem authority.

[Hostile contracts](../audits/lean-pccmin-dead-support-context0.test.mjs)
reject fabricated support, invented boundary inputs, discarded interfaces,
missing framing, non-proper acceptance, weakened or supplied theorem types,
project-axiom injection, changed fingerprints and widened claims.

No fixed checkpoint or global gate closes. Formal artefact coverage changes
independently of the risk-weighted proof-completion estimate. The canonical
[progress ledger](../status/PROOF_PROGRESS.json) remains the single source of
current scores; historical rows retain their original scope.

Publication decision: defer PNPLabs. This bounded physical replacement component
does not change the coherent published M231 bottom line. Meaningful verified
submilestone notifications continue independently of website cadence.
