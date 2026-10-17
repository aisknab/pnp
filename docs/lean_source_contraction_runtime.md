# Polynomial source contraction and witness replay

Current coordinate: `PNP-FORMAL-RECONSTRUCTION-STATUS-2026-10-18-284`.

The source-contraction phase now has a closed finite-machine implementation with polynomial runtime and output bounds. A separate replay machine reconstructs a checked original certificate when a model of the remaining core is available. Finding that model remains open.

Formal artefact coverage: 260 of 262 current scoped publication rows earned.
Risk-weighted proof completion estimate: 40%.
Uncertainty range: 20% to 40%.
Global gates closed: 0 of 5.

## Exact scope

For every raw input bitstring, the closed source-construction finite machine halts within its encoded-input polynomial bound and emits exactly the canonical source-derived contraction packet, with polynomial output size. On a decoded source system, the actual remaining core is satisfiable exactly when the original input is in CNFSAT. A separate closed finite-machine replay endpoint returns the exact canonical optional answer on every raw request. For the history generated from the actual source system, it lifts any genuine remaining-core model to a certificate accepted by the original source checker, with physical replay time bounded polynomially in the original input length. Projection and recovery preserve original models; source-generated history is not a caller-supplied correctness certificate.

## Limits

A genuine model of the remaining core is still required for certificate recovery; this work does not find that model. A positive-dimensional stopped core remains unknown and may be satisfiable or unsatisfiable. The replay runtime bound starts from the canonical encoded request; a further finite-machine request assembler is not claimed. These are polynomial source-construction and witness-replay endpoints, not a complete residual decision procedure, manuscript residual-band minimizer, unconditional SaturatePositive, BCELReady or ZeroSlack, exact polynomial PCCMin, concrete CNFSAT membership in P, or eligible root theorem. P = NP is not proved.

## Checked endpoints

| Endpoint | Input and checked result |
| --- | --- |
| Source construction | Every raw source bitstring produces the exact canonical contraction packet within a polynomial physical-machine bound. The encoded output size is polynomial in the original input length. |
| Model preservation | For the system decoded from the actual normalizer output, a model of the remaining core exists exactly when the original source is satisfiable. |
| Closed replay | Every raw replay request produces its exact canonical optional answer. For the source-generated history, projection and recovery preserve genuine original models. |
| Certificate recovery | A genuine remaining-core model yields a correctly sized original certificate accepted by the actual source checker. Replay time is bounded in the original source length, starting from the canonical encoded request. |

The [public contract](../lean/PNP/Concrete/ResidualReduction/SourceReductionRuntime.lean) connects the [source machine](../lean/PNP/Concrete/ResidualReduction/SourceReductionPolynomial.lean), [physical replay endpoint](../lean/PNP/Concrete/ResidualReduction/SourceReplayEndpointPolynomial.lean), [generated-history maps](../lean/PNP/Concrete/ResidualReduction/SourceReplayEndpointGenerated.lean) and [original-input accounting](../lean/PNP/Concrete/ResidualReduction/SourceReplayEndpointBudget.lean). The histories, contraction choices and reduction data come from the actual source; they are not supplied as correctness certificates.

In the `SourceReductionRuntime` namespace, the certificate and physical-time contract is:

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

The `model` premise is deliberate. A positive-dimensional stopped core still returns `none`, not a guessed negative answer. The encoded request includes the complete generated history and a dimension-bounded witness. Accounting for that size closes the original-input bound for replay, but does not by itself implement an additional request-building machine.

## Verification boundary

The explicit project root imports the implementation and its independent kernel contracts. The [root axiom transcript](../lean-audit/PNPSourceContractionRuntimeAxiomAudit.lean) covers the reviewed public endpoint declarations; only `propext` and `Quot.sound` occur. Existing component execution regressions are retained without a second standalone copy of the same proof checks.

The [source contract](../audits/lean-source-contraction-runtime0.test.mjs) checks the reviewed implementation and regression sources, root reachability and hostile changes to the input, source checker, runtime bound and retained model premise. The [publication contract](../audits/lean-source-contraction-runtime-publication0.test.mjs) freezes the compiled kernel types, modules, axiom sets, scope and score boundary. These tests do not generate their expected type fingerprints from their own observed result.

## Connection to the overall proof

The manuscript's residual-band exact-minimization argument requires a complete algorithm, not just a bound on the number of contractions. This result supplies actual encoded construction and physical execution bounds for a full reduction phase, including runs that stop with a nonempty core. It does not discharge global route coverage, unconditional activation or the terminal decision obligation.

M282 and M283 remain historical evidence for their original theorem interfaces. Their row-local limitations are not rewritten: M284 records the additional runtime guarantees separately, while the global complete-algorithm runtime gate remains open.

## Progress and publication

M284 retires the encoded-construction and physical-runtime obligations for the source-contraction phase and closed-request witness replay. The remaining core is not solved, a genuine terminal model is still required for certificate recovery, and a further request-assembly machine is not claimed. These endpoint bounds are not the complete PCCMin algorithm or its unconditional runtime and exactness proof. No fixed load-bearing checkpoint changes state; weights, checkpoint statuses, proof estimate and uncertainty are unchanged.

Publication decision: publish one major PNPLabs batch after the exact core merge passes verification. The source-construction and witness-replay endpoints now have complete finite-machine polynomial runtime contracts, a substantial general capability beyond a count of local milestones. Include pending earned M283 evidence in the same source-pinned site update. No fixed load-bearing checkpoint changes state, and no global gate closes.

See the [integration plan](./plans/2026-10-18-source-contraction-runtime.md), [canonical progress ledger](../status/PROOF_PROGRESS.json), [source-bound partial reducer](./lean_residual_reducer.md), [contraction class](./lean_source_contraction_class.md) and [pinned manuscript](../archive/legacy-v0/ARCHIVE.json).
