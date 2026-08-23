# Concrete locked-NAND threshold publication

The historical report's theorem G asserts the locked-NAND SAT decision
boundary.  The relevant unbounded obligation is not another fixed circuit or
finite truth-table case: one uniform encoded builder must work for every input
bitstring and preserve SAT membership while staying inside a proved
polynomial-time machine model.

`PNP.Main.locked_nand_threshold` is the report-facing theorem for that exact
boundary.  Its kernel type is:

```text
PNP.Concrete.ReducesTo
  PNP.Concrete.CNFSAT
  PNP.Concrete.LockedNAND.EncodedLockedNANDThreshold
```

The witness is the already-audited composition of the literal CNF-to-NAND
compiler and strict locked-NAND parser/emitter.  `PolynomialReduction` carries
the finite function program, explicit polynomial runtime and output-size
bounds, and all-bitstring correctness.  Malformed source strings therefore
remain part of the theorem and fail closed; no well-formedness promise or
caller-supplied semantic certificate is introduced.

The compiled axiom transcript for the theorem contains only Lean's permitted
standard axioms `propext` and `Quot.sound`. It contains neither of the current
two disclosed project axioms. M186 makes `PNP.LockedNANDThreshold` the exact
concrete endpoint and consumes this theorem directly; no string handle or
caller-supplied reduction field remains.

This earns the global locked-NAND construction-and-threshold milestone.  It
does not supply a polynomial decider for the concrete target, complete the
residual-band/ZeroSlack/PCCMin path, prove concrete CNFSAT NP-hardness, or
establish `PNP.Main.p_eq_np`.  Those remain the downstream blockers.

## Mechanically generated publication evidence

- Lean inventory: `PNP-LEAN-THEOREM-INVENTORY-2026-08-12-129`
- publication map: `PNP-FORMAL-PUBLICATION-MAP-2026-08-12-130`
- reconstruction status: `PNP-FORMAL-RECONSTRUCTION-STATUS-2026-08-12-130`
- public surface: `PUBLIC-SURFACE-BASELINE-2026-08-10-CONCRETE-LOCKED-NAND-THRESHOLD-121`
- canonical report: `PNP-CANONICAL-FORMAL-RECONSTRUCTION-REPORT-2026-08-12-130`

The compiled inventory records 27,573 declarations, 14,360 theorems, 7,314
assumption-free theorems, 15,002 excluded private declarations, 247
source-closure modules, and 2,557 reviewed milestone candidates. Its
17,787,380 canonical bytes have SHA-256
`859ef0595f1eeea872518b0f399a788225e3a2ed9fefe987c6ae5bd6b3783aaf`;
the exact Lean source closure has SHA-256
`4608b17afe6e8d0be3f7f6e0fae526025c0050f64dca9670e71ae89f9f27aa7c`.

The 829,327-byte publication map contains 108 milestones: 106 earned and two
deliberately unearned. It pins 2,557 theorem types and has SHA-256
`f076b8f813c2877d7a03b7090151d4c9db9f4793a5c4f40fbdc5125c82808ed8`.
The generated 2,084,476-byte status has SHA-256
`1a4609a63dd44da92cfc4558d1cef0db60430b26942cc6b3e2d199eb35d66ed9`.
The canonical 218,897-byte TeX source has SHA-256
`2f3aeaa0801283edbcb713f74567d133ea4598e3b5eb04541ac083d31fbf7546`;
its deterministic 85-page, 455,853-byte A4 PDF has SHA-256
`fedbffc7877c0cf4da70f6eea77395f7ee413e48917a80ee3ea5f24d9c325fec`.

At that pinned publication coordinate, the concrete publication gate remained
false and all four then-disclosed project axioms, all five remaining blockers,
unset activation fingerprints, and the absence of `PNP.Main.p_eq_np` were
retained. The current inventory is generated separately and must not be
inferred from these historical byte coordinates.

```sh
lake build PNP.Concrete.LockedNANDThresholdPublication
lake env lean -DwarningAsError=true \
  lean-audit/PNPConcreteLockedNANDThresholdPublicationAxiomAudit.lean
node --test \
  audits/lean-concrete-locked-nand-threshold-publication0.test.mjs
```
