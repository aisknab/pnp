# M272 plan: computational recoding in complete source-only programs

## Legacy anchor and dependency edge

The pinned manuscript's Section 6.1 R2 and Section 6.2 N3 require recoding to
compose with Section 4 physical ownership and charges and Section 6.3 splicing.
This milestone reconstructs the computational finite-circuit case of that edge:
actual encoder and decoder circuits become actions of the complete program
checker, rather than externally supplied semantic functions or correctness
certificates. It does not claim the full manuscript profile semantics or all
R2/N3 obligations.

The unbounded objects are arbitrary finite carrier widths, literal NAND
encoder/decoder circuits, event dependency graphs and complete offered programs.
The existing raw circuit format is reused. Correctness, order, cost, causal
bounds and ownership are computed or proved from those objects, not supplied as
authority.

## Exact construction and theorem boundary

- `GateRenaming.decode_encode` supplies the existing structural route's exact
  finite-bijection encoding. It is supporting evidence, not a separate milestone.
- `WireCarrierRecoding.check_iff` characterizes both full inverse equations.
  `result_output`, `result_field` and `result_gate_balance` bind the actual
  appended circuits and both physical-normalization results.
- The finite syntactic dependency guard is equivalent to preserving causal
  bounds for every natural-number input labelling. It must check hidden fields
  as well as ordinary outputs; semantic invertibility alone is insufficient.
- The state operation retains the entire pending snapshot function and charges
  every literal encoder/decoder gate. It does not create or discharge obligations.
- Physical ownership follows the actual append and normalization maps. Encoder
  and decoder allocations have distinct derived phases. Removed allocations
  remain charged and are lifted through the preceding complete-program ledger.
- `WireRecodingInput.decode_encode` returns the exact typed implementation from
  the existing raw format. Both dimensions, every gate and every output reference
  must decode. `execute_success_iff` requires both decodes plus the computed
  inverse and causal checks.
- The expanded complete-program compiler still rejects failed tails and unclosed
  obligations. Its general semantic, lifecycle, gate-balance and ownership
  theorems remain applicable.
- `WireOpenCertificate.verify_exists_iff` and `verify_sound` still require
  proper support, the complete accepted program, final closure and strict
  physical saving. Reversible conversion does not itself imply a saving.

The inverse checker enumerates all field valuations. Finite termination is not
a polynomial-runtime theorem. Constant propagation, NAND sharing and pruning
do not promise semantic inverse-cancellation; regressions must count the actual
remaining gates rather than assume a round trip physically erases its circuits.

## Source and expectation matrix

Prepare producer and consumer changes together before their validation.

| Producer | Consumers to reconcile | First verification boundary |
| --- | --- | --- |
| Six new encoding, recoding, causal, state, ownership and raw-input modules | Explicit root imports, reviewed declaration sets, source contracts and hostile mutations | General source/assumption contracts and existing targeted Lean evidence |
| Three extended open-program modules | All older closed-interface audits located by path and declaration, new mixed-program regression | Source-only old/new contracts before compilation |
| Proper-support execution with recoding | Certificate runtime expectations, exact theorem and axiom names | Positive saving, complete costs, failed tails, open obligations, no saving and whole-support rejection |
| Reviewed theorem set | Lean inventory producer, required-name consumer, publication row, fingerprint keys and exact axiom audit | Name-set comparison before inventory extraction |
| Compiled evidence and claim boundary | Frozen kernel types/axioms, conservative status fields, both status-validator field sets and publication mutations | Exact compiled contract and widened-claim rejection |
| Audit/package/workflow changes | Closed package fixture, aggregate verifier, literal durable workflow blocks | Package source mutations, workflow syntax/size, then exact new commands |
| Canonical status and progress ledger | Current summary regions, README FAQ, progress explanation and report generator | Generate current values first, then focused current-document checks |

Keep the source-only and sealed-publication checks separate. A missing new
inventory seal during development is not grounds to weaken a publication
validator or launch a broad suite that is known to require that seal.

## Verification order and reusable evidence

1. Complete mathematical source and paired positive/negative expectations.
   Targeted construction, whole-program and certificate development checks have
   passed; this is not yet an earned release.
2. Freeze reviewed source contracts. Reconcile every old consumer of the changed
   modules, and prepare explicit root imports and all theorem-name producers and
   consumers together. Check intended new files for whitespace before sealing.
3. Run cheap source/name/root/workflow preflights. Reuse targeted evidence whose
   exact source, dependency closure, toolchain and boundary remain unchanged.
4. Build the changed dependency chain and explicit root; extract compiled
   inventory and exact axiom evidence. Derive fingerprints only from this result.
5. Reconcile status, the fixed-weight progress ledger and current narrative.
   Generate current summary/FAQ metrics and report outputs from canonical data.
   Preserve the M230 complete-builder and M231 NP-completeness provenance anchors.
6. Run the focused current-progress/current-documentation checks and the new
   publication mutation family before the deduplicated broad release suite.
   A stale count is an agent preparation error, not a reason to weaken a test.
7. Follow normal draft review, required checks, manual merge and exact-merge
   reproduction. Reuse identical-tree mathematical evidence where permitted;
   do not rerun core Lean work as website verification.

Do not preselect emitted theorem totals, source-closure hashes, report metadata
or evidence-row coverage. Obtain them from the canonical generators, then update
all active consumers before verification. Historical coordinates stay unchanged.

## Remaining obligations and publication decision

This validates offered computational programs; it does not discover a successful
certificate for every input. Full manuscript profiles and remaining rule
families, full VerifyDW, ChargeSoundness and Package E, terminal-derived families,
global routing, unconditional SaturatePositive, BCELReady and ZeroSlack, exact
general PCCMin, uniformly polynomial encoded runtime/output/certificate bounds,
deterministic CNFSAT in P and the eligible root remain open.

No fixed weighted checkpoint or global gate closes from this integration.
The proof-completion estimate remains governed by
[`status/PROOF_PROGRESS.json`](../../status/PROOF_PROGRESS.json), independently
of any additional publication row.

Publication decision: defer PNPLabs. This extends the offered-program checker,
not the public global-proof bottom line. Keep the coherent published source pin
and its metrics unchanged. Reassess at a major end-to-end capability, weighted
checkpoint, gate transition or necessary correction, not an accumulated row count.
