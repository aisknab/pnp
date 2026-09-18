# Computational recoding in complete source-only replacement programs

M272 connects literal reversible field recoding to complete mixed replacement
programs and proper-support certificate verification. Its manuscript anchors
are Section 6.1 R2 recoding, Section 6.2 N3 normalization, Section 4
physical ownership and charges, and Section 6.3 composed splicing in the
[pinned report](../archive/legacy-v0/ARCHIVE.json).

## Computed recoders and complete histories

The existing raw circuit codec validates both field widths and every gate
and output coordinate of both actual NAND recoders. An exact inverse check
tests both full inverse equations. It enumerates every field valuation;
finite decidability is not a polynomial-time result. A separate syntactic
dependency check covers arbitrary natural-number input labels, ordinary
outputs and hidden fields. Semantic reversibility does not imply that check.

Both literal circuits are appended to the actual carrier and normalized.
Every allocated encoder/decoder gate is charged, and only actual normalizer
deletions are counted as removals. Physical ownership follows those append
and deletion maps with separate derived encoder/decoder allocation phases.
The complete program retains earlier owner identities and all historical
charges and removals. Recoding preserves the exact pending snapshot function
and neither creates nor discharges an obligation.

The complete certificate checker rejects a malformed or invalid later step,
an open final ledger, an improper support, or a lack of strict signed saving.
A reversible recoder pair need not physically cancel under the implemented
normalizer; the regression for that case records its real added gates and
rejects the certificate. A successful positive fixture restores its pending
obligation and includes a separate genuinely saving computational action.

The supporting structural code construction proves that every finite gate
bijection has an exact raw-swap encoding using at most one swap per gate.
That encoding completeness does not grant a second milestone or weighted point.

## Source and verification interfaces

- [Structural encoding](../lean/PNP/NANDGateRenamingEncoding.lean) and
  [literal carrier recoding](../lean/PNP/NANDWireCarrierRecoding.lean).
- [Exact causal guard](../lean/PNP/NANDCausalGuard.lean),
  [state snapshots](../lean/PNP/NANDWireRecodingState.lean),
  [physical ownership](../lean/PNP/NANDWireRecodingOwnership.lean), and
  [raw input interface](../lean/PNP/NANDWireRecodingInput.lean).
- [Complete programs](../lean/PNP/NANDWireOpenProgram.lean),
  [historical ownership](../lean/PNP/NANDWireOpenProgramOwnership.lean), and
  [proper-support certificates](../lean/PNP/NANDWireOpenCertificate.lean).
- [Source contracts](../audits/lean-computational-recoding0.test.mjs),
  [compiled publication contracts](../audits/lean-computational-recoding-publication0.test.mjs),
  and [explicit-root axiom audit](../lean-audit/PNPComputationalRecodingAxiomAudit.lean).

Run `npm run audit:m272` after status and progress generation.
The durable workflow separately executes the explicit-root axiom audit and
seven regression modules for encoding, carrier, state, ownership, raw input,
complete programs and certificates. Runtime fixtures are regression evidence,
not proof authority. Reuse compiled root and inventory evidence when only
release documentation, status or workflow consumers change.

## Reviewed publication boundary

As of PNP-FORMAL-RECONSTRUCTION-STATUS-2026-09-18-272:

For arbitrary finite computational wire carriers, literal NAND encoder and decoder circuits, dependency graphs and complete offered replacement programs, raw recoding actions reuse the existing circuit format and validate both dimensions and every gate and output reference. A complete finite check derives both inverse equations. An independent exact syntactic dependency guard covers all ordinary outputs and hidden fields for every natural-valued input labelling. Actual encoder and decoder gates are appended, normalized and charged; actual compiler maps determine deletions and disjoint allocation identities. Recoding retains the entire pending snapshot function and cannot create or discharge an obligation. Complete-program execution lifts those physical identities through prior history, preserves full semantics, costs, causal invariants and creation-to-discharge bindings, and rejects an invalid later action rather than accepting a prefix. The proper-support certificate verifier still requires complete execution, a closed final ledger and strict actual saving. The existing structural decoder also has a constructive exact encoding of every finite gate bijection with at most one swap per gate. Callers supply raw data, not correctness, causal, ordering, ownership or cost authority.

This checks offered computational programs, not a successful certificate-discovery strategy for every input. The inverse checker enumerates all field valuations; finite termination and a bounded structural swap list do not establish uniformly polynomial encoded runtime or certificate size. Semantic reversibility does not imply physical cancellation or strict saving. Full manuscript profiles, all R1-R9 and N1-N10 rules, full VerifyDW, ChargeSoundness and Package E remain open. Terminal-family derivation, global route coverage, unconditional SaturatePositive, BCELReady and ZeroSlack, exact general PCCMin, deterministic CNFSAT in P and the eligible root remain open. No fixed weighted checkpoint or global proof gate closes, and P = NP is not proved.

Formal artefact coverage: 248 of 250 current scoped publication rows earned.
Risk-weighted proof completion estimate: 40%.
Uncertainty range: 20% to 40%.
Global gates closed: 0 of 5.

Publication decision: defer. This extends checked offered computational replacement programs with literal recoding, but does not establish global certificate discovery, full manuscript profiles or a polynomial algorithm. No fixed weighted checkpoint or global gate changes, and the public global-proof bottom line remains unchanged. Preserve the coherent M264 website pin and batch pending core evidence at the next major publication.

The [fixed progress ledger](../status/PROOF_PROGRESS.json) is authoritative.
Its risk-weighted estimate is neither confidence that the route is correct nor
a delivery or time-remaining estimate. See the
[implementation and verification plan](plans/2026-09-18-computational-recoding-integration.md).
