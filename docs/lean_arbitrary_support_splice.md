# Computed arbitrary-support literal NAND replacement

M249 reconstructs the physical substitution edge of section 2 Compatible
replacement and section 5 N1 topological reordering in the manuscript pinned by
[the archive manifest](../archive/legacy-v0/ARCHIVE.json).

## Computed objects and general guarantees

The raw graph compiler reads each NAND gate's two actual source fields. It scans
the remaining nodes in canonical order, emits only a ready node, removes that
exact node, and maintains an injective source-to-program position map. Every
successful compilation includes every original node exactly once. Every nonempty
stuck remainder has an unresolved predecessor for each remaining node.
Compilation succeeds exactly when the actual dependency relation is well founded.
Every original ordered output is reconnected through the computed positions.

The support-splice constructor computes the original exterior gates, actual
incoming boundary and outgoing interface, every replacement connection, and the
complete ordered global output tuple. Selected producers are rebound through the
corresponding replacement output; unselected producers retain their exact exterior
positions. There is no unresolved-source constant fallback.

No frame, order, wiring map or acyclicity certificate is supplied to the constructor.
For an accepted literal splice, physical size is exactly the exterior-gate count
plus replacement size, including replacements larger than the original support.
If the replacement has the extracted support's complete open Boolean function,
the resulting NAND program preserves every original output. A strict local
physical saving becomes a strict whole-program saving.

The equivalence premise constrains the replacement's open function; it does not
certify whole-circuit correctness. Whole-circuit correctness is derived from the
actual graph equations and the checked compiler.

For actual production saturation, the existing predecessor-closure theorem
derives a primary-input-only boundary. A rank placing replacement gates before
the exterior's original gate order proves acyclicity. Consequently production
splicing succeeds without a caller proof. It agrees in size and complete semantics
with the already checked M237 physical constructor; that earlier result is not
re-earned here.

## Cycles and remaining obligations

Equal open Boolean functions do not by themselves guarantee acyclic literal wiring.
The regression uses an interleaved support whose equivalent replacement creates a
dependency cycle. Its raw NAND equations have a solution, but the compiler correctly
rejects it: a simultaneous Boolean solution is not an acyclic direct-wire program.
This is not a contradiction of the manuscript's unconstructed complete carrier
premises.

The result is physical substitution, not full-profile preservation or complete
manuscript normalization. The manuscript carrier, R5/R6-R8 obligation lifecycle,
arbitrary-support Pull/Expand materializer identities and complete Package E remain
open. The compiler does not find a minimum replacement. A finite node-count
termination argument is not a total encoded-size polynomial runtime theorem.
Unconditional SaturatePositive, BCELReady and ZeroSlack, exact polynomial PCCMin,
deterministic CNFSAT in P and the eligible root remain open.

No fixed checkpoint or global gate closes.

## Reviewed interfaces and evidence

The twenty-four general interfaces below have exact compiled type fingerprints.
Their axiom dependencies are contained in `propext` and `Quot.sound`; no
project-specific axiom or `Classical.choice` is required.

- `PNP.DirectWire.RawNandCompilationState.readSource_sound`
- `PNP.DirectWire.RawNandCompilationState.readGate_sound`
- `PNP.DirectWire.RawNandReadyStep.apply_remaining_lt`
- `PNP.DirectWire.RawNandCompilationStop.unresolved_predecessor`
- `PNP.DirectWire.RawNandCompilationStop.complete_of_wellFounded`
- `PNP.DirectWire.CompiledRawNandGraph.wellFounded`
- `PNP.DirectWire.compileRawNandGraph_success_iff`
- `PNP.DirectWire.compileRawNandGraph_failure_iff`
- `PNP.DirectWire.CompiledRawNandGraph.candidate_gateCount`
- `PNP.DirectWire.CompiledRawNandGraph.candidate_semantics`
- `PNP.DirectWire.ArbitrarySupportSplice.result_gateCount`
- `PNP.DirectWire.ArbitrarySupportSplice.compile_success_iff`
- `PNP.DirectWire.ArbitrarySupportSplice.compile_failure_iff`
- `PNP.DirectWire.ArbitrarySupportSplice.replacementSource_eval`
- `PNP.DirectWire.ArbitrarySupportSplice.originalSource_eval`
- `PNP.DirectWire.ArbitrarySupportSplice.values_solution`
- `PNP.DirectWire.ArbitrarySupportSplice.result_semantics`
- `PNP.DirectWire.ArbitrarySupportSplice.exterior_accounting`
- `PNP.DirectWire.ArbitrarySupportSplice.result_exact_accounting`
- `PNP.DirectWire.ArbitrarySupportSplice.result_strict_gain`
- `PNP.DirectWire.ArbitrarySupportSplice.graph_rank_decreases`
- `PNP.DirectWire.ArbitrarySupportSplice.graph_wellFounded_of_primaryBoundary`
- `PNP.DirectWire.ArbitrarySupportSplice.production_compiles`
- `PNP.DirectWire.ArbitrarySupportSplice.production_agreement`

The explicit root imports the new construction. The exact durable workflow checks
its theorem axioms and runs the general-type and guarded runtime regressions.
Source and compiled hostile tests reject supplied schedules, narrowed dimensions,
missing dependencies, unresolved-source defaults, partial success, invented gate
counts, changed outputs, weakened theorem types and inflated publication claims.

The bounded fixtures include reverse numeric/execution order, disconnected and
empty graphs, repeated/input/constant outputs, self and mutual cycles, a partly
ready cyclic remainder, safe interleaving, equivalent-but-cyclic rewiring, a smaller
non-closed support, larger production replacement, empty/full supports and zero
input/output dimensions. Runtime execution is test evidence, not theorem authority.

## Progress and publication cadence

Formal artefact coverage: 225 of 227 current scoped publication rows earned.
Risk-weighted proof completion estimate: 40%. Uncertainty range: 20% to 40%. Global gates closed: 0 of 5.

Formal artefact coverage describes the evidence ledger, not proof completion.
The fixed-weight proof estimate is not confidence, a probability of success, or
a time estimate. New local evidence does not automatically close a load-bearing
checkpoint.

Publication decision: defer PNPLabs. This physical component does not change the
coherent published M231 bottom line; the core milestone remains independently
verified and recorded for a future major publication batch.

Sources: [raw graph compiler](../lean/PNP/NANDTopologicalCompiler.lean),
[actual support splice](../lean/PNP/NANDArbitrarySupportSplice.lean),
[axiom audit](../lean-audit/PNPArbitrarySupportSpliceAxiomAudit.lean),
[regressions](../lean-regression/PNPArbitrarySupportSplice.lean), and
[implementation plan](plans/2026-09-12-computed-arbitrary-support-splice.md).
