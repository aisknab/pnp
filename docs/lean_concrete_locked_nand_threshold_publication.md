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
standard axioms `propext` and `Quot.sound`.  It contains none of the four
disclosed project axioms.  In particular, it does not use the legacy
`PNP.LockedNANDThreshold` string handle, whose old conditional bridge remains
publication-ineligible.

This earns the global locked-NAND construction-and-threshold milestone.  It
does not supply a polynomial decider for the concrete target, complete the
residual-band/ZeroSlack/PCCMin path, prove concrete CNFSAT NP-hardness, or
establish `PNP.Main.p_eq_np`.  Those remain the downstream blockers.

## Mechanically generated publication evidence

- Lean inventory: `PNP-LEAN-THEOREM-INVENTORY-2026-08-10-122`
- publication map: `PNP-FORMAL-PUBLICATION-MAP-2026-08-11-123`
- reconstruction status: `PNP-FORMAL-RECONSTRUCTION-STATUS-2026-08-11-123`
- public surface: `PUBLIC-SURFACE-BASELINE-2026-08-10-CONCRETE-LOCKED-NAND-THRESHOLD-121`
- canonical report: `PNP-CANONICAL-FORMAL-RECONSTRUCTION-REPORT-2026-08-10-122`

The compiled inventory records 26,540 declarations, 13,884 theorems, 7,159
assumption-free theorems, 14,935 excluded private declarations, 240
source-closure modules, and 2,487 reviewed milestone candidates. Its
17,207,898 canonical bytes have SHA-256
`f86ecb4b91dcc4bbd6988aba15b03dc5998a965dc21aabf830d40b41c871f434`;
the exact Lean source closure has SHA-256
`6adc25ee3d9920358ea8803adf47ab94d8e70c91026b8756bb45dbad1dda577d`.

The 805,053-byte publication map contains 101 milestones: 99 earned and two
deliberately unearned. It pins 2,487 theorem types and has SHA-256
`531a4dbd6d7925582aed1e6011d917e8dfdaf5576e1c259f63cd76a897d2aa5c`.
The generated 2,024,772-byte status has SHA-256
`cb5b4146385a6aa8d91fc1778007e7ea418a382237d5e706277c2d7a362172ac`.
The canonical 209,712-byte TeX source has SHA-256
`924606c880420091e8aff17f185ea52e8080c7729c3a1fba520f678e848be83a`;
its deterministic 82-page, 447,683-byte A4 PDF has SHA-256
`44d07e868371fedb86f48492f857a26d9a38b86b9b8e81a2ace8ba13c96eeafe`.

The concrete publication gate remains false. All four disclosed project
axioms, all five remaining blockers, unset activation fingerprints, and the
absence of `PNP.Main.p_eq_np` are retained.

```sh
lake build PNP.Concrete.LockedNANDThresholdPublication
lake env lean -DwarningAsError=true \
  lean-audit/PNPConcreteLockedNANDThresholdPublicationAxiomAudit.lean
node --test \
  audits/lean-concrete-locked-nand-threshold-publication0.test.mjs
```
