# Computed physical-charge partition and introduction provenance

M236 constructs the complete physical-NAND charge ledger of a computed
saturation. It connects individual fresh insertions to exact whole-support
accounting without replacing the existing executor or support extractor.

## Exact theorem boundary

The [physical-charge ledger module](../lean/PNP/ResidualTerminalPhysicalChargeLedger.lean)
defines `TerminalPhysicalCharge`, distinguishes inherited seed provenance from
actual generated rule/dependent provenance, and computes both the ledger and
its lookup from the real normalized seed and saturation trace.

The five interfaces apply at arbitrary finite dimensions, systems and seeds:

- `terminalSaturatePhysicalCharges_nodup` proves that the physical gate
  identifiers in the complete ledger are duplicate-free.
- `terminalSaturatePhysicalCharges_complete` equates ledger gate membership
  with physical gate-record membership in the computed saturated support.
- `terminalSaturatePhysicalCharges_provenance` recovers each entry's seed
  origin or actual generating event, with its exact rule and dependent,
  active context and fresh required gate.
- `terminalSaturatePhysicalChargeProvenance?_iff` proves that lookup returns
  exactly the provenance of the corresponding computed ledger entry.
- `terminalCandidateSaturatePhysicalCharges_size` additionally quantifies
  over arbitrary candidates and executable terminal models. It equates the
  entire computed ledger length with the unchanged extractor's support size.

The ledger includes every seed gate, even if no event generates it. Only
physical NAND gates are charged; proof-only metadata is excluded. No supplied
charge list, completeness certificate, freshness premise or ownership
certificate is substituted for the computation.

## Provenance is not manuscript-wide ownership

Introduction provenance is not the fixed manuscript-wide ownership map.
It can depend on the normalized seed and traversal. Active requesting pairs
are not assigned manuscript owners. Several physical charges can share one
requesting dependency; unique charge identity does not mean that a requester
owns at most one gate.

The pinned manuscript's section 4 charge partition includes more than the
physical-NAND gate universe reconstructed here. Materializer grouping,
profile charges and cross-support ownership transport remain separate proof
obligations. The [plan](plans/2026-09-11-physical-charge-ledger.md) records the
section 3, section 4 and section 10 RW-SaturatePositive dependency edges.

## Regressions and assumption audit

The [permanent regression](../lean-regression/PNPResidualTerminalPhysicalChargeLedger.lean)
applies every interface at arbitrary dimensions. Execution fixtures cover
inherited and generated charges, repeated seeds, absent lookup, a cyclic
multi-gate dependency, generated metadata, metadata-only traces and zero
dimensions.

A nonconstant NAND gate requested by two outputs has two active requesting
pairs while support size, full minimum and quotient minimum all grow from
zero to one. The old classifier reports its requester-count obstruction.
This distinguishes that classifier's requester list from assigned ownership;
it is not a contradiction of the manuscript or a new global proof result.
The executor, extractor, observer, reference minima and classifier are unchanged.

The [explicit-root audit](../lean-audit/PNPResidualTerminalPhysicalChargeLedgerAxiomAudit.lean)
checks all five interfaces. Their axiom closures contain only `propext` and
`Quot.sound`, with no project-specific axiom or classical choice.
The [hostile contracts](../audits/lean-residual-terminal-physical-charge-ledger0.test.mjs)
reject supplied, finite, incomplete, duplicated, weakened and assumption-backed
substitutes, widened ownership claims and kernel-type fingerprint drift.

## Remaining proof burden

The executable observer and profile model remain supplied data. Influence and
semantic minima use exhaustive finite reference constructions; no polynomial
runtime is proved.

The exact physical charge partition does not establish full-minimum growth,
quotient bounds, complete closure safety, obligation discharge, global route
coverage or an input-derived terminal family. Unconditional SaturatePositive,
BCELReady and ZeroSlack, complete polynomial PCCMin runtime and certificate
bounds, deterministic CNFSAT in P and the eligible root theorem remain open.
The publication gate remains false. No fixed weighted checkpoint or global
gate closes.

Formal artefact coverage: 212 of 214 current scoped publication rows earned.
Risk-weighted proof completion estimate: 40%. Uncertainty range: 20% to 40%. Global gates closed: 0 of 5.

These separate measures come from the
[canonical progress ledger](../status/PROOF_PROGRESS.json). Neither is confidence
that `P = NP` is true, a probability of success or a time estimate.

Publication decision: defer. Preserve the coherent M231 PNPLabs source pin
until a major publication is warranted. Meaningful core submilestone and
release notifications continue independently.
