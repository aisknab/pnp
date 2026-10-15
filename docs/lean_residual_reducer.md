# Source-bound partial residual reduction and certificate recovery

Current coordinate: `PNP-FORMAL-RECONSTRUCTION-STATUS-2026-10-15-282`.

Formal artefact coverage: 258 of 260 current scoped publication rows earned.
Risk-weighted proof completion estimate: 40%.
Uncertainty range: 20% to 40%.
Global gates closed: 0 of 5.

## Exact scope

For every native sparse residual system, a computed translation retains all positive, linear and product constraints, including duplicate-term parity and coordinate order. A dimension-decreasing source-derived chain preserves models, links every step to its preceding residual, preserves the row count, and supplies inverse parameter and satisfying-source maps. For every original bitstring whose actual serialized normalizer output decodes to a system, the remaining core is satisfiable exactly when that original input is in CNFSAT; a remaining model reconstructs a correctly sized encoded certificate accepted by the actual output checker. The original-input partial verdict is sound for both true and false answers and returns unknown when positive dimension remains. At most 30 times the source bitstring length plus 12 reductions occur; this bounds steps, not execution work. No chosen contraction, family, route coverage certificate or correctness premise is supplied by a caller.

## Limits

Stopping exhausts the computed finite affine/line/plane selector menu, not the whole class of possible contractions. An unknown core can be satisfiable or unsatisfiable; useful reduction on every instance and all-input decision are not proved. The chain-length bound is not a polynomial bound on total encoded construction, storage or runtime. This is not the completed manuscript residual-band minimizer, unconditional SaturatePositive, BCELReady or ZeroSlack, exact polynomial PCCMin, deterministic CNFSAT membership in P, or the eligible root theorem. P = NP is not proved.

## Checked interface

The [public interface](../lean/PNP/Concrete/ResidualReducer.lean) binds the complete source system, repeated reduction, certificate encoding and original-input partial verdict. The following theorem types are copied from that interface in its namespace.

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

The decoded-packet premise identifies the actual normalizer output; it is not a caller-supplied correctness or route-completeness certificate. The source-family translation retains the positive equation, every linear guard and every product row. Duplicate coefficients cancel by parity, and the certificate coordinate order agrees with the existing packet checker.

The reduction preserves all residual rows and links each selected step to the preceding family. Its parameter projection/lift maps are inverses on all residual parameters. The reverse source reconstruction requires a satisfying source assignment; it is not claimed for arbitrary non-models.

The [axiom audit](../lean-audit/PNPResidualReducerAxiomAudit.lean) imports the explicit repository root and checks all sixteen public theorem closures. Only `propext` and `Quot.sound` occur. The [Lean regressions](../lean-regression/PNPResidualReducer.lean) check sixteen uniform contracts and ten kernel guards, including satisfiable and unsatisfiable unknown cores, retained constraints, duplicate-term parity, coordinate order and model-only reconstruction. These finite guards provide regression coverage, not milestone credit.

The [frozen source contract](../audits/lean-residual-reducer0.test.mjs) seals the compiled dependency closure and rejects weakened types, omitted constraints and supplied authority. The [publication contract](../audits/lean-residual-reducer-publication0.test.mjs) independently freezes the sixteen kernel type fingerprints, axiom closures, exact scope, status fields and score boundary. Tests do not regenerate their own source or type expectations.

## Connection to the overall proof

M281 already constructs the complete input-derived residual packet in polynomial time. This milestone attaches a computed, model-preserving reduction chain to that exact representation and recovers valid encoded certificates from remaining models. It supplies justified partial answers, not a total residual decision procedure.

The historical residual-band exact-minimization claim is still not reconstructed by this result. Exhaustion of the implemented affine/line/plane menu does not establish coverage of every possible contraction or useful progress on every nonterminal instance. A bounded number of steps alone does not bound encoded coefficient construction, selector computation, history storage or total execution time. Those obligations must be proved for the complete algorithm before runtime or solver credit can be awarded.

The manuscript remains a fallible reference. The [support-slack correction](./lean_compatible_support_slack_obstruction.md) and [fixed-window obstruction](./lean_fixed_window_coverage_obstruction.md) retain their exact scope; this alternative construction does not erase either result.

## Progress and publication

M282 closes the connection from the actual complete normalized source system to a model-preserving repeated residual reduction and checked encoded certificate recovery. Its original-input verdict is sound but partial: positive-dimensional stopped cores remain unknown, and stopping proves only exhaustion of the computed selector menu. The linear number-of-steps bound is not a complete encoded-runtime theorem. Useful all-input progress, whole-contraction-class coverage, unconditional ZeroSlack and exact polynomial PCCMin remain open. No fixed load-bearing checkpoint changes state; weights, checkpoint statuses, proof estimate and uncertainty are unchanged.

Publication decision: publish after verified core merge. The complete source-bound partial reduction and certificate recovery form a substantial general capability beyond a local lemma or fixed instance. Publish one batch from the exact core merge, preserve prior corrections and show unknown outcomes and unresolved solver/runtime obligations explicitly. This does not change the risk-weighted proof estimate.

See the [integration plan](./plans/2026-10-15-source-bound-partial-residual-reducer.md), [canonical progress ledger](../status/PROOF_PROGRESS.json), [complete serialized normalizer](./lean_serialized_normalizer.md) and [pinned manuscript](../archive/legacy-v0/ARCHIVE.json).
