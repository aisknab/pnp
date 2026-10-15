# M282: source-bound partial residual reduction

Coordinate: `PNP-FORMAL-RECONSTRUCTION-STATUS-2026-10-15-282`.

Formal artefact coverage: 258 of 260 current scoped publication rows earned.
Risk-weighted proof completion estimate: 40%.
Uncertainty range: 20% to 40%.
Global gates closed: 0 of 5.

## Legacy anchor and selected dependency

The manuscript pinned by [ARCHIVE.json](../../archive/legacy-v0/ARCHIVE.json), at `final-pnp-proof-report-docs-hardened-7072f8d-sealed`, claims residual-band exact minimization, historically represented by `PNP.ResidualBandExactMinimization`. The active unresolved obligation is `Formal.ResidualBandMinimizer`, on the route to unconditional ZeroSlack and a complete deterministic solver. The manuscript is a fallible reference, not theorem authority; removing its former project axiom did not prove the missing claim.

The exact upstream checked edge is M281's `PNP.Concrete.SerializedNormalizer.residual_system_iff`. The selected new edge connects every actual normalized native system to a source-derived, model-preserving repeated reduction, then recovers encoded certificates from remaining models. This is an independently justified partial construction, not a claim that the legacy exact minimizer has been completed.

## Unbounded abstraction and exact theorem types

For every native sparse residual system, a computed translation retains all positive, linear and product constraints, including duplicate-term parity and coordinate order. A dimension-decreasing source-derived chain preserves models, links every step to its preceding residual, preserves the row count, and supplies inverse parameter and satisfying-source maps. For every original bitstring whose actual serialized normalizer output decodes to a system, the remaining core is satisfiable exactly when that original input is in CNFSAT; a remaining model reconstructs a correctly sized encoded certificate accepted by the actual output checker. The original-input partial verdict is sound for both true and false answers and returns unknown when positive dimension remains. At most 30 times the source bitstring length plus 12 reductions occur; this bounds steps, not execution work. No chosen contraction, family, route coverage certificate or correctness premise is supplied by a caller.

These are source-copied types in `PNP.Concrete.ResidualReducer`; the public facade fixes all supporting definitions.

```lean
theorem residual_source_iff (input : BitString) (c : Nat)
    (D : NativeSparseSystem.System c)
    (decoded : NativeOutputPacket.codec.decode (SerializedNormalizer.output input) =
      some (.system c D)) :
    (∃ z, models (reduce D).core z = true) ↔ CNFSAT input

theorem recover_certificate (input : BitString) (c : Nat)
    (D : NativeSparseSystem.System c)
    (decoded : NativeOutputPacket.codec.decode (SerializedNormalizer.output input) =
      some (.system c D))
    (z : Point (reduce D).dimension) (satisfied : models (reduce D).core z = true) :
    (recoverCertificate D z).length = 2*c ∧
      NativeSerializedNormalizer.checkEncoded (SerializedNormalizer.output input)
        (recoverCertificate D z) = true

theorem step_bound (input : BitString) (c : Nat) (D : NativeSparseSystem.System c)
    (decoded : NativeOutputPacket.codec.decode (SerializedNormalizer.output input) =
      some (.system c D)) :
    (reduce D).history.length ≤ 30*input.length+12

theorem decision_true_sound (input : BitString) (answer : decision input = some true) :
    CNFSAT input

theorem decision_false_sound (input : BitString) (answer : decision input = some false) :
    ¬ CNFSAT input

theorem decision_unknown (input : BitString) (c : Nat)
    (D : NativeSparseSystem.System c)
    (decoded : NativeOutputPacket.codec.decode (SerializedNormalizer.output input) =
      some (.system c D))
    (remaining : (reduce D).dimension ≠ 0) :
    decision input = none
```

The arbitrary native system interface is linked to every original bitstring through equality with the actually decoded output. No supplied family, correctness premise or completeness certificate substitutes for construction. Model-only reconstruction and the explicit unknown case are part of the interface, not limitations that tests may remove.

## Verification and release sequence

1. Preserve the exact mathematical statements while integrating the general modules into the public namespace. Reuse the unchanged baseline cache and private verification evidence; compile the new namespace, facade and explicit root.
2. Keep the Lean reviewed-name producer and JavaScript consumer aligned before compiled inventory extraction. Freeze the sixteen exact type fingerprints only after the root build and assumption audit.
3. Add uniform typed contracts, kernel semantic guards, frozen source contracts and hostile publication tests. Reconcile both status maps, package scripts, closed script fixture, verifier list and the exact durable workflow block before broad tests.
4. Derive current coverage and generated outputs from the compiled inventory and publication ledger. Keep all fixed checkpoint states and weights unchanged, record the reason, and preserve historical milestones.
5. Run targeted publication checks, syntax-check and execute the exact durable workflow block, then the required deduplicated core verification. Normal PR, post-merge and exact-object reproduction checks remain distinct mandatory boundaries.
6. Merge the verified core change first. Publish one PNPLabs batch bound to that exact merge, with byte mirrors, rendering, source pins and provenance checks but no second Lean build.
7. Deploy only the verified site merge and independently verify production. External review is validation evidence, not a mathematical premise; none is claimed for this release.

## Remaining blockers and score decision

Stopping exhausts the computed finite affine/line/plane selector menu, not the whole class of possible contractions. An unknown core can be satisfiable or unsatisfiable; useful reduction on every instance and all-input decision are not proved. The chain-length bound is not a polynomial bound on total encoded construction, storage or runtime. This is not the completed manuscript residual-band minimizer, unconditional SaturatePositive, BCELReady or ZeroSlack, exact polynomial PCCMin, deterministic CNFSAT membership in P, or the eligible root theorem. P = NP is not proved.

M282 closes the connection from the actual complete normalized source system to a model-preserving repeated residual reduction and checked encoded certificate recovery. Its original-input verdict is sound but partial: positive-dimensional stopped cores remain unknown, and stopping proves only exhaustion of the computed selector menu. The linear number-of-steps bound is not a complete encoded-runtime theorem. Useful all-input progress, whole-contraction-class coverage, unconditional ZeroSlack and exact polynomial PCCMin remain open. No fixed load-bearing checkpoint changes state; weights, checkpoint statuses, proof estimate and uncertainty are unchanged.

The next mathematical priority is a justified mechanism for useful general residual progress or a rigorous resolution of the remaining coverage and complete-runtime obligations. Another fixed instance, supplied-data sidecar or longer selector prefix is not a substitute.

## Publication decision

Publication decision: publish after verified core merge. The complete source-bound partial reduction and certificate recovery form a substantial general capability beyond a local lemma or fixed instance. Publish one batch from the exact core merge, preserve prior corrections and show unknown outcomes and unresolved solver/runtime obligations explicitly. This does not change the risk-weighted proof estimate.
