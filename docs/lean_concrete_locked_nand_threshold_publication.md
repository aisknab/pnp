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

- Lean inventory: `PNP-LEAN-THEOREM-INVENTORY-2026-08-11-127`
- publication map: `PNP-FORMAL-PUBLICATION-MAP-2026-08-11-128`
- reconstruction status: `PNP-FORMAL-RECONSTRUCTION-STATUS-2026-08-11-128`
- public surface: `PUBLIC-SURFACE-BASELINE-2026-08-10-CONCRETE-LOCKED-NAND-THRESHOLD-121`
- canonical report: `PNP-CANONICAL-FORMAL-RECONSTRUCTION-REPORT-2026-08-11-128`

The compiled inventory records 27,348 declarations, 14,272 theorems, 7,281
assumption-free theorems, 14,996 excluded private declarations, 245
source-closure modules, and 2,540 reviewed milestone candidates. Its
17,687,580 canonical bytes have SHA-256
`3d770295f55293a4775921e965907ef6e59faa3129fc5f387bf3f24c19fa6d85`;
the exact Lean source closure has SHA-256
`dbf73b2875e5aa8a8c9dafb5c054869bc453b911ca4d72e33288fe0527b4db02`.

The 823,299-byte publication map contains 106 milestones: 104 earned and two
deliberately unearned. It pins 2,540 theorem types and has SHA-256
`fd5e93f1f17311d4713e643e74831cab2a66951f6f89256edfe075ea76819a21`.
The generated 2,069,206-byte status has SHA-256
`d07f55de837091f1f70a4d871e5d943980c793df9a4e48be25b4ac26057fd258`.
The canonical 216,608-byte TeX source has SHA-256
`ff3fb948c0e05a854f58fb5b36f61d7a64fc735d402927723301b7a9d1c0c244`;
its deterministic 84-page, 453,568-byte A4 PDF has SHA-256
`28f268221e1087afa38b00708b818a029e2200fa8c4280b33d7a217ac2959933`.

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
