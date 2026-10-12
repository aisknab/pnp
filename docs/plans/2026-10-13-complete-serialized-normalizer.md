# M281: complete polynomial serialized normalization

Coordinate: `PNP-FORMAL-RECONSTRUCTION-STATUS-2026-10-13-281`.

Formal artefact coverage: 257 of 259 current scoped publication rows earned.
Risk-weighted proof completion estimate: 40%.
Uncertainty range: 20% to 40%.
Global gates closed: 0 of 5.

## Legacy anchor and selected dependency

The manuscript pinned by [ARCHIVE.json](../../archive/legacy-v0/ARCHIVE.json), at `final-pnp-proof-report-docs-hardened-7072f8d-sealed`, states the Traceable normalization theorem in “Verifier-readable proof calculus, normalization, and splice”. That theorem claims semantics, minimum and slack preservation and backward gain transport for `NormalizeOrGain`. It is a fallible specification, not Lean authority. The [checked support-slack correction](../lean_compatible_support_slack_obstruction.md) and [fixed-window obstruction](../lean_fixed_window_coverage_obstruction.md) are not repaired by relabelling a new representation as that normalizer.

The selected alternative edge is the complete construction from every encoded source input to an exactly equivalent, fully serialized residual packet. The proposed downstream path is normalizer composition with a general sound, complete polynomial residual solver. This milestone closes the construction edge only. No theorem claims preservation of the manuscript semantic minimum, global routing, or polynomial residual solution.

## Unbounded abstraction and exact theorem types

For every source bitstring, a concrete finite-machine refinement computes the complete source-derived serialized normalization packet and halts within a polynomial in the encoded input length. The packet has a polynomial encoded-size bound, strict decode roundtrip and malformed-input convention. Its encoded certificate language is equivalent to CNFSAT on that same input; satisfiable inputs have a certificate of at most 30 times the input length plus 12 bits. Every system packet retains all residual equations, and every model packet yields a satisfying source assignment. The packaged polynomial reduction uses the actual serialized machine output. No construction, completeness or correctness certificate is supplied by a caller.

These are source-copied theorem types in `PNP.Concrete.SerializedNormalizer`; the public facade fixes all supporting definitions.

```lean
theorem output_eq (input : BitString) :
    output input = NativeSerializedNormalizer.serialize input

theorem halts (input : BitString) :
    boundedDecide rawRefinement.machine
      (rawRefinement.timeBound.eval (BitString.size input)) input ≠ .timeout

theorem satisfiability_iff (input : BitString) :
    (∃ certificate, NativeSerializedNormalizer.checkEncoded (output input) certificate = true) ↔
      CNFSAT input

theorem certificate_bound (input : BitString) (satisfiable : CNFSAT input) :
    ∃ certificate, certificate.length ≤ 30 * input.length + 12 ∧
      NativeSerializedNormalizer.checkEncoded (output input) certificate = true

theorem residual_system_iff (input : BitString) (rows : Nat) (D : NativeSparseSystem.System rows)
    (decoded : NativeOutputPacket.codec.decode (output input) = some (.system rows D)) :
    (∃ certificate : BitString, certificate.length = 2 * rows ∧
      D.Satisfied (MeasuredBits.rowValues rows certificate)) ↔ CNFSAT input

theorem reduction_correct (input : BitString) :
    CNFSAT input ↔ language (output input)
```

## Verification and release sequence

1. Reuse the completed explicit-root build, strict axiom review, general Lean regressions and frozen-source hostile tests for unchanged proof sources.
2. Synchronize the Lean inventory producer, required-name contract, publication row and independently reviewed type fingerprints before the live inventory export.
3. Export the compiled inventory once; derive the real source closure, evidence coverage and generated status. Update current documents and dependent expectations before broad validation.
4. Run focused publication mutations and the exact durable workflow block, then the deduplicated core validation union. Normal PR and exact-object reproduction boundaries remain mandatory.
5. Merge the verified core change first. Publish one PNPLabs batch pinned to its exact merge, checking site rendering, byte mirrors and provenance without repeating Lean compilation.
6. Deploy only the verified site merge and independently verify production. External review may add validation evidence but is not a premise or a prerequisite for a kernel-checked local theorem. No external review has been obtained for this release.

## Remaining blockers and score decision

This constructs and encodes an equivalent residual problem; a system packet is not an unsatisfiability verdict. Short certificate existence does not provide certificate discovery. The result does not implement the manuscript NormalizeOrGain minimizer, solve all residual systems, establish global route coverage or unconditional ZeroSlack, or prove exact polynomial PCCMin. Its polynomial bounds cover the complete normalizer, not a complete SAT solver. Deterministic CNFSAT membership in P and the eligible root theorem remain absent; P = NP is not proved.

M281 closes the complete source-to-serialized-residual construction edge: one input-derived finite machine has exact packet semantics and encoded-input polynomial runtime and output bounds. It does not discover a certificate or decide arbitrary residual systems, and does not reconstruct manuscript semantic minimization. The fixed reduction track was already earned; normalizer bounds do not retire the complete PCCMin runtime obligation. No fixed load-bearing checkpoint changes state; weights, checkpoint statuses, proof estimate and uncertainty are unchanged.

## Publication decision

Publication decision: publish after verified core merge. This is one complete all-input construction with literal-machine runtime and encoding guarantees, not another fixed prefix or local sidecar. Batch pending core evidence and preserve the published corrections. The website must distinguish this new general capability from the still-open solver and retain the unchanged risk-weighted estimate.
