# Computed physical output cones and unused-gate pruning

M244 reconstructs the physical unused-gate deletion subcase of the pinned
manuscript's Package E structural congruence and traceable normalization.
It is a computed physical unused-gate pruning stage, not complete manuscript N1-N10 normalization.

## Construction

No support or correctness certificate is supplied by the caller. For any finite
direct-wire NAND implementation, the pass reads its actual ordered output word,
seeds every gate-valued output, and computes the least predecessor-closed gate
support. It reuses the existing executable terminal saturation and checked support
extractor rather than introducing another closure algorithm or NAND compiler.

The proof shows that the computed incoming boundary contains only original
primary inputs. Those inputs are renamed back to their original coordinates.
Every output is then reconnected in its original position, including constants,
primary input wires and repeated gate-valued outputs. Only gates are deleted;
the original input/output shape is preserved.

The physical-only saturation system uses an empty profile index. This explicitly
does not derive the manuscript's complete metadata/profile support and must not
be substituted for full-profile governance.

## Reviewed universal interfaces

- `PNP.DirectWire.outputConeRecords_output`
- `PNP.DirectWire.outputConeRecords_closed`
- `PNP.DirectWire.outputConeRecords_least`
- `PNP.DirectWire.outputConeRecords_noExternalGate`
- `PNP.DirectWire.outputConeImplementation_equivalent`
- `PNP.DirectWire.outputConeImplementation_gateCount_le`
- `PNP.DirectWire.outputConeImplementation_exact_accounting`
- `PNP.DirectWire.outputConeImplementation_referenceMinimum`
- `PNP.DirectWire.outputConeImplementation_residualSlack`
- `PNP.DirectWire.outputConeImplementation_strictGain_iff`
- `PNP.DirectWire.outputConeNormalizer_checked`

All eleven theorems are built through the explicit root with only `propext`
and `Quot.sound`. Gate cost is exact: retained gates plus deleted gates equal
the original physical count. Equivalent semantics makes the reference minimum
invariant, so residual slack decreases by exactly the number of deleted gates.
A positive deletion is surfaced as a checked physical gain through the existing
`PCCMinTotalNormalizer` interface.

## Limits and negative cases

A no-deletion branch does not imply semantic minimality. A NAND whose one input
is constant false remains structurally output-reachable even though its output
is always true and has a zero-gate equivalent implementation. Thus full physical
reachability is not a ZeroSlack criterion.

An arbitrary full-profile observer can also distinguish the physical gate count
before and after pruning. Boolean equivalence therefore does not establish
full-profile equality, a proper Package E witness or arbitrary witness pullback.
The M239 firewall and the complete downstream profile obligations remain intact.

The pass uses actual finite work-list closure and support extraction;
reference minimum occurs in specification theorems, not in execution.
No complete encoded-size polynomial execution theorem for the PCCMin construction
is claimed. Global family derivation, full normalization, route completeness,
SaturatePositive, BCELReady, unconditional ZeroSlack and the total PCCMin oracle
remain open.

The regression file checks universal theorem types and guarded runtime fixtures
for unused chains, shared predecessors, repeated ordered outputs, constant and
primary-input outputs, zero-input circuits and empty output shapes. It rejects
confusion between no deletion and minimality, and between physical equivalence
and full-profile equality. Runtime execution is test evidence, not theorem authority.

## Progress and publication

Formal artefact coverage: 220 of 222 current scoped publication rows earned.
Risk-weighted proof completion estimate: 40%. Uncertainty range: 20% to 40%. Global gates closed: 0 of 5.

No fixed checkpoint or global gate closes. The added row measures formal
artefact coverage only. PNPLabs publication is deferred until a major verified
capability changes the public bottom line.

See the [milestone plan](plans/2026-09-12-derived-output-cone-pruning.md),
[canonical progress ledger](../status/PROOF_PROGRESS.json) and
[conditional final-report bridge](lean_concrete_final_report_bridge.md).
