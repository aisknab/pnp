# M284 polynomial source contraction and witness replay

Coordinate: `PNP-FORMAL-RECONSTRUCTION-STATUS-2026-10-18-284`.

Formal artefact coverage: 260 of 262 current scoped publication rows earned.
Risk-weighted proof completion estimate: 40%.
Uncertainty range: 20% to 40%.
Global gates closed: 0 of 5.

## Legacy anchor and selected dependency

The manuscript pinned by [ARCHIVE.json](../../archive/legacy-v0/ARCHIVE.json), in its residual-band exact-minimization section, requires an executable uniformly polynomial procedure. The active blocker remains `Formal.ResidualBandMinimizer`. The manuscript is a fallible research reference, not theorem authority.

M282 proved source-derived contraction semantics and a bound on the number of contractions. M283 covered a precisely defined contraction class. Neither step count nor class coverage bounds the complete encoded discovery, row construction, history storage and witness replay. This milestone closes those runtime obligations for the reduction phase and closed-request replay without assuming a useful contraction or a terminal model exists on every input.

## Unbounded abstraction and exact target

For every raw input bitstring, the closed source-construction finite machine halts within its encoded-input polynomial bound and emits exactly the canonical source-derived contraction packet, with polynomial output size. On a decoded source system, the actual remaining core is satisfiable exactly when the original input is in CNFSAT. A separate closed finite-machine replay endpoint returns the exact canonical optional answer on every raw request. For the history generated from the actual source system, it lifts any genuine remaining-core model to a certificate accepted by the original source checker, with physical replay time bounded polynomially in the original input length. Projection and recovery preserve original models; source-generated history is not a caller-supplied correctness certificate.

The selected interface covers every raw source bitstring and every raw replay request. For actual source-generated requests, replay time is bounded in the original source length. In `PNP.Concrete.ResidualReduction.SourceReductionRuntime`, the exact certificate boundary is:

```lean
theorem recover_certificate_runtime (input : BitString) (c : Nat) (D : NativeSparseSystem.System c)
    (decoded : NativeOutputPacket.codec.decode (SerializedNormalizer.output input) = some (.system c D))
    (z : Point (NativeSource.reduceSystem D).dimension)
    (model : models (NativeSource.reduceSystem D).core z = true) :
    ∃ steps ≤ SourceReplayEndpointBudget.nativeRuntimePolynomial.eval input.length,
      ∃ certificate,
        boundedDecide SourceReplayEndpointPolynomial.rawRefinement.machine steps
          (SourceReplayRequest.codec.encode (recoveryRequest c D z)) ≠ .timeout ∧
        SourceReplayEndpointOutput.codec.decode
          (machineOutput SourceReplayEndpointPolynomial.rawRefinement.machine steps
            (SourceReplayRequest.codec.encode (recoveryRequest c D z))) = some (some certificate) ∧
        certificate.length = 2 * c ∧
        NativeSerializedNormalizer.checkEncoded (SerializedNormalizer.output input) certificate = true
```

The source-output, source-halting, output-size, satisfiability-preservation, replay-output, replay-halting and unresolved-core theorems are pinned alongside this contract. Original-model projection/recovery and the original-input physical projection bound complete the reviewed interface.

## Verification and integration

1. Complete the finite programs, their physical refinements, source-size accounting and independent kernel contracts. Retain actual source-derived histories and the explicit terminal-model premise.
2. Synchronize the explicit root, Lean reviewed-name producer and JavaScript consumer before the compiled inventory extraction. Review and freeze the compiled type fingerprints and allowed axiom sets.
3. Add one publication row for the complete phase, not one row per helper. Reconcile the package script, closed script fixture, verifier, both status maps, progress ledger, current documentation and exact durable workflow block before broad validation. Derive coverage and report metadata from canonical outputs.
4. Reuse the unchanged successful component and root evidence. Run focused source and hostile publication checks, the normal core validations, and the exact added workflow block. Do not rerun the component suites through duplicate standalone regression files.
5. Use the normal draft PR, complete checks, manual ready and merge, post-merge checks and exact-object reproduction sequence. These are distinct evidence boundaries, not replacements for source validation.
6. After the verified core merge, publish one source-pinned PNPLabs batch including pending M283 evidence. PNPLabs checks its mirrors, claims, links, rendered surfaces and deployment provenance without recompiling the already verified core Lean source.

## Remaining blockers and scoring

A genuine model of the remaining core is still required for certificate recovery; this work does not find that model. A positive-dimensional stopped core remains unknown and may be satisfiable or unsatisfiable. The replay runtime bound starts from the canonical encoded request; a further finite-machine request assembler is not claimed. These are polynomial source-construction and witness-replay endpoints, not a complete residual decision procedure, manuscript residual-band minimizer, unconditional SaturatePositive, BCELReady or ZeroSlack, exact polynomial PCCMin, concrete CNFSAT membership in P, or eligible root theorem. P = NP is not proved.

M284 retires the encoded-construction and physical-runtime obligations for the source-contraction phase and closed-request witness replay. The remaining core is not solved, a genuine terminal model is still required for certificate recovery, and a further request-assembly machine is not claimed. These endpoint bounds are not the complete PCCMin algorithm or its unconditional runtime and exactness proof. No fixed load-bearing checkpoint changes state; weights, checkpoint statuses, proof estimate and uncertainty are unchanged.

The next mathematical priority is a justified general way to decide the positive-dimensional stopped core, with a constructive algorithm, correctness and encoded-size polynomial bounds. A further finite example, supplied-data sidecar or extra evidence row does not close that obligation.

## Publication decision

Publication decision: publish one major PNPLabs batch after the exact core merge passes verification. The source-construction and witness-replay endpoints now have complete finite-machine polynomial runtime contracts, a substantial general capability beyond a count of local milestones. Include pending earned M283 evidence in the same source-pinned site update. No fixed load-bearing checkpoint changes state, and no global gate closes.

See the [checked endpoints and limits](../lean_source_contraction_runtime.md) and [progress ledger](../../status/PROOF_PROGRESS.json).
