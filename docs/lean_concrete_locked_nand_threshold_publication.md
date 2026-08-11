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

- Lean inventory: `PNP-LEAN-THEOREM-INVENTORY-2026-08-11-124`
- publication map: `PNP-FORMAL-PUBLICATION-MAP-2026-08-11-125`
- reconstruction status: `PNP-FORMAL-RECONSTRUCTION-STATUS-2026-08-11-125`
- public surface: `PUBLIC-SURFACE-BASELINE-2026-08-10-CONCRETE-LOCKED-NAND-THRESHOLD-121`
- canonical report: `PNP-CANONICAL-FORMAL-RECONSTRUCTION-REPORT-2026-08-11-125`

The compiled inventory records 26,851 declarations, 14,025 theorems, 7,197
assumption-free theorems, 14,947 excluded private declarations, 240
source-closure modules, and 2,511 reviewed milestone candidates. Its
17,400,943 canonical bytes have SHA-256
`80dae39e58e0053129c34e0105fc9635777e2920a1d93529f14493813508c772`;
the exact Lean source closure has SHA-256
`44067b7a25d092dab39173d5563593fb56921adf0eb3b5d7294c0b5e64b7af2a`.

The 813,470-byte publication map contains 103 milestones: 101 earned and two
deliberately unearned. It pins 2,511 theorem types and has SHA-256
`3385b374bdbc737e8c6808698dc0284ad84ac0850d7bd62b7079d5f6d5b2cfed`.
The generated 2,044,745-byte status has SHA-256
`acd3acd30a52590ed16966c55b62b8aaf1d2d5985b08ea627057a0d9ab4db07f`.
The canonical 212,960-byte TeX source has SHA-256
`92f911ee8d3286aba5f75b476d3691260355ad7c0a906c3478b8daf68f2c9d44`;
its deterministic 83-page, 450,819-byte A4 PDF has SHA-256
`f84e248a5cd842af25965669f1e8387d8adfbfad4a2e29828798cf9f855151fc`.

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
