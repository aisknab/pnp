# Complete search for balanced source-scalar quadratic contractions

Current coordinate: `PNP-FORMAL-RECONSTRUCTION-STATUS-2026-10-16-283`.

Formal artefact coverage: 259 of 261 current scoped publication rows earned.
Risk-weighted proof completion estimate: 40%.
Uncertainty range: 20% to 40%.
Global gates closed: 0 of 5.

## Exact scope

For every finite family of factored Boolean source equations in every positive dimension, every balanced selected-source-scalar translation whose pullback preserves quadratic degree on every source row implies that the actual affine/line/plane selector returns a step; the existing checked step-soundness contract applies. Semantic quadratic closure is equivalent to the exact coefficient obstruction criterion and to quadratic closure through the computed quotient decoder. The actual decoder composed with the encoder equals the balanced source retraction on every ambient point. A stopped selector has no contraction in this precisely defined class; no finite-menu membership or caller-supplied coverage premise is required.

## Limits

Contraction existence remains a premise. This class consists only of balanced translations by a fixed direction with scalar equal to an XOR of selected source equations and with quadratic pullbacks of all rows. It does not include arbitrary contraction maps, higher-degree transformations or general residual decision procedures. A stopped core may still be satisfiable. No useful contraction on every input, complete residual solver, polynomial encoded construction or runtime, manuscript residual-band minimizer, unconditional SaturatePositive, BCELReady or ZeroSlack, exact polynomial PCCMin, concrete CNFSAT membership in P, or eligible root theorem is proved. P = NP is not proved.

## Defined class and checked interface

The scalar is the XOR of selected equations from the actual source family, including affine constants. Translation by the chosen direction toggles that scalar; each full source row, including unselected rows, must remain quadratic after pullback. The semantic definition does not assume a line, plane, menu membership or coverage certificate.

The [class definition](../lean/PNP/Concrete/ResidualReduction/SourceContractionClass.lean), [coverage proof](../lean/PNP/Concrete/ResidualReduction/SourceClassCompleteness.lean) and [actual decoder bridge](../lean/PNP/Concrete/ResidualReduction/SourceClassChart.lean) expose these types in `PNP.Concrete.ResidualReduction.SourceClass`:

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

A vanishing third difference is proved equivalent to the existence of quadratic coefficients by dimension induction and finite unit probes. The coefficient obstruction then forces source derivatives into a line or a plane already searched by the computed selector. The existence premise is retained: coverage of the class is not a proof that it is nonempty on every input.

The actual decoder composed with the encoder equals the source retraction on every ambient point, not only on satisfying assignments. The existing `globalStep_sound` theorem supplies step soundness; the independent regression contract combines it with the new existence result.

The [explicit-root axiom audit](../lean-audit/PNPSourceContractionClassAxiomAudit.lean) checks all ten reviewed theorem closures; only `propext` and `Quot.sound` occur. The [Lean regressions](../lean-regression/PNPSourceContractionClass.lean) check six arbitrary-dimensional contracts and four hostile finite guards: a satisfiable exhausted class, balance without degree closure, a cubic obstruction in an unselected row, and preservation of affine constants. Finite guards are regression evidence, not milestone credit.

The [source contract](../audits/lean-source-contraction-class0.test.mjs) freezes the compiled dependency closure. The [publication contract](../audits/lean-source-contraction-class-publication0.test.mjs) freezes the ten kernel types, axiom sets, scope, status fields and score boundary. Neither test regenerates its expectations from its own observed result.

## Connection to the overall proof

The manuscript residual-band exact-minimization claim needs both justified coverage and useful progress, together with complete encoded-size and runtime bounds. This result removes the menu-relative premise for one complete, precisely stated contraction class. It does not decide remaining cores or establish the existence and complexity obligations. The historical M282 publication row and its reviewed scope remain intact; new status fields name the additional class guarantee explicitly.

## Progress and publication

M283 removes the supplied finite-menu eligibility boundary for the complete balanced selected-source-scalar quadratic contraction class and connects the exact semantic criterion to the actual decoder. It does not construct a useful contraction on every input or decide an exhausted residual core, and does not prove complete encoded-runtime bounds. No fixed load-bearing checkpoint changes state; weights, checkpoint statuses, proof estimate and uncertainty are unchanged.

Publication decision: defer PNPLabs synchronization. This milestone certifies the completeness of the existing search for a precisely defined contraction class without adding an all-input decision capability, closing a fixed weighted checkpoint or changing a global gate. Keep the existing verified site source pin coherent and include this result in the next major publication batch.

See the [integration plan](./plans/2026-10-16-source-scalar-contraction-class.md), [canonical progress ledger](../status/PROOF_PROGRESS.json), [source-bound partial reducer](./lean_residual_reducer.md) and [pinned manuscript](../archive/legacy-v0/ARCHIVE.json).
