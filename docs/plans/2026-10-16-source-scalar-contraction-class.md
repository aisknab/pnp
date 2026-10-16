# M283: complete source-scalar quadratic contraction search

Coordinate: `PNP-FORMAL-RECONSTRUCTION-STATUS-2026-10-16-283`.

Formal artefact coverage: 259 of 261 current scoped publication rows earned.
Risk-weighted proof completion estimate: 40%.
Uncertainty range: 20% to 40%.
Global gates closed: 0 of 5.

## Legacy anchor and selected dependency

The manuscript pinned by [ARCHIVE.json](../../archive/legacy-v0/ARCHIVE.json) claims residual-band exact minimization, historically represented by `PNP.ResidualBandExactMinimization`. The active blocker remains `Formal.ResidualBandMinimizer`. The manuscript is a fallible reference, not theorem authority. Removing its former axiom did not prove the missing claim.

M282 supplies a sound source-derived partial reducer but its coverage theorem required membership in the computed affine/line/plane menu. The selected edge derives that eligibility for every balanced selected-source-scalar translation with quadratic pullbacks of all source rows, and proves equivalence with the actual quotient decoder. It does not replace a missing existence theorem with a supplied coverage certificate.

## Unbounded abstraction and exact target

For every finite family of factored Boolean source equations in every positive dimension, every balanced selected-source-scalar translation whose pullback preserves quadratic degree on every source row implies that the actual affine/line/plane selector returns a step; the existing checked step-soundness contract applies. Semantic quadratic closure is equivalent to the exact coefficient obstruction criterion and to quadratic closure through the computed quotient decoder. The actual decoder composed with the encoder equals the balanced source retraction on every ambient point. A stopped selector has no contraction in this precisely defined class; no finite-menu membership or caller-supplied coverage premise is required.

The types below are copied from the checked `SourceClass` namespace. All source dimensions and finite families are arbitrary; the selector theorem covers positive dimensions.

```lean
theorem globalStep_complete_for_semantic {n : Nat} (F : Family (n+1))
    (h : ∃ w v, SemanticContraction F w v) : ∃ s, globalStep F = some s

theorem globalStep_none_no_semantic {n : Nat} (F : Family (n+1))
    (hn : globalStep F = none) : ¬ ∃ w v, SemanticContraction F w v

theorem semantic_iff_coefficient {n : Nat} (F : Family n)
    (w : Point F.length) (v : Point n) :
    SemanticContraction F w v ↔ CoefficientContraction F w v

theorem semantic_iff_chart {n : Nat} (F : Family (n+1))
    (w : Point F.length) (v : Point (n+1)) (c : Fin (n+1) × Point n)
    (hc : chooseChart v = some c) :
    SemanticContraction F w v ↔ Balanced F w v ∧ ChartQuadraticClosure F w c
```

## Verification and integration

1. Build the three general modules and explicit root, then audit the ten named theorem closures and run six independent general contracts plus four hostile guards. Keep the exact statements unchanged when removing unwanted tactic-introduced assumptions.
2. Freeze the compiled source closure, kernel type hashes and axiom sets. Align the Lean reviewed-name producer, JavaScript consumer, publication row and fingerprint-key set before extracting the inventory.
3. Reconcile package scripts, the closed script fixture, verifier list, both status maps, current summaries, canonical progress ledger and the durable workflow block before broad validation. Derive counts from the generated ledger; preserve historical records and fixed checkpoints.
4. Reuse the exact source-bound root evidence and cache. Run focused hostile contracts first, then normal core verification. Syntax-check and execute the exact added workflow shell block. PR checks, post-merge checks and exact-object reproduction remain distinct required boundaries.
5. Use the normal draft PR, complete checks, manual ready/merge and exact-merge reproduction sequence. Do not advance the website pin for this supporting milestone.

## Remaining blockers and scoring

Contraction existence remains a premise. This class consists only of balanced translations by a fixed direction with scalar equal to an XOR of selected source equations and with quadratic pullbacks of all rows. It does not include arbitrary contraction maps, higher-degree transformations or general residual decision procedures. A stopped core may still be satisfiable. No useful contraction on every input, complete residual solver, polynomial encoded construction or runtime, manuscript residual-band minimizer, unconditional SaturatePositive, BCELReady or ZeroSlack, exact polynomial PCCMin, concrete CNFSAT membership in P, or eligible root theorem is proved. P = NP is not proved.

M283 removes the supplied finite-menu eligibility boundary for the complete balanced selected-source-scalar quadratic contraction class and connects the exact semantic criterion to the actual decoder. It does not construct a useful contraction on every input or decide an exhausted residual core, and does not prove complete encoded-runtime bounds. No fixed load-bearing checkpoint changes state; weights, checkpoint statuses, proof estimate and uncertainty are unchanged.

The next mathematical priority is useful general residual progress or a rigorously justified way to decide the exhausted core, with complete construction and complexity obligations. Another fixed instance or supplied-data sidecar is not a substitute.

## Publication decision

Publication decision: defer PNPLabs synchronization. This milestone certifies the completeness of the existing search for a precisely defined contraction class without adding an all-input decision capability, closing a fixed weighted checkpoint or changing a global gate. Keep the existing verified site source pin coherent and include this result in the next major publication batch.

See the [theorem and exact limits](../lean_source_contraction_class.md) and [progress ledger](../../status/PROOF_PROGRESS.json).
