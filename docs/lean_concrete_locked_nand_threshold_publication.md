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

- Lean inventory: `PNP-LEAN-THEOREM-INVENTORY-2026-08-11-128`
- publication map: `PNP-FORMAL-PUBLICATION-MAP-2026-08-11-129`
- reconstruction status: `PNP-FORMAL-RECONSTRUCTION-STATUS-2026-08-11-129`
- public surface: `PUBLIC-SURFACE-BASELINE-2026-08-10-CONCRETE-LOCKED-NAND-THRESHOLD-121`
- canonical report: `PNP-CANONICAL-FORMAL-RECONSTRUCTION-REPORT-2026-08-11-129`

The compiled inventory records 27,442 declarations, 14,309 theorems, 7,290
assumption-free theorems, 14,999 excluded private declarations, 246
source-closure modules, and 2,548 reviewed milestone candidates. Its
17,726,895 canonical bytes have SHA-256
`612342db90e5887e2da6417963946437c82a14003f48deeddeae03d50caf637f`;
the exact Lean source closure has SHA-256
`4fde46c2f495422c43f5d2eb3ed80500c097a94b511aaecc74f5e8da979cd910`.

The 826,175-byte publication map contains 107 milestones: 105 earned and two
deliberately unearned. It pins 2,548 theorem types and has SHA-256
`9093dd1bdc84405be1748831ad59b98a60aabbd80d389f26f38f889de44770ea`.
The generated 2,076,560-byte status has SHA-256
`79c3ef6dace2f95cdad66add48c105e4ed5f95609b9c2819533685f63ed941aa`.
The canonical 217,706-byte TeX source has SHA-256
`e43ad410bc6e10f4e5d22d24c559b236e5698eb54b8b6b2659e2d0b3a8e4989c`;
its deterministic 85-page, 455,104-byte A4 PDF has SHA-256
`f48bc615866790d08151198272e89c9e68f8e1fd404ae46700ced768f42aa70c`.

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
