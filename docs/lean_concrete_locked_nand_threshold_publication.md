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

- Lean inventory: `PNP-LEAN-THEOREM-INVENTORY-2026-08-11-126`
- publication map: `PNP-FORMAL-PUBLICATION-MAP-2026-08-11-127`
- reconstruction status: `PNP-FORMAL-RECONSTRUCTION-STATUS-2026-08-11-127`
- public surface: `PUBLIC-SURFACE-BASELINE-2026-08-10-CONCRETE-LOCKED-NAND-THRESHOLD-121`
- canonical report: `PNP-CANONICAL-FORMAL-RECONSTRUCTION-REPORT-2026-08-11-127`

The compiled inventory records 27,193 declarations, 14,163 theorems, 7,264
assumption-free theorems, 14,995 excluded private declarations, 243
source-closure modules, and 2,530 reviewed milestone candidates. Its
17,583,178 canonical bytes have SHA-256
`884d84ade0af3ce3d588c6bba011fd21ec0fb7fdf0b0d1fee5d156f051002a8c`;
the exact Lean source closure has SHA-256
`a6aaa00d8faa48ed1d51bb0346363956d4cd2de8a14ecbe043458831d896dd02`.

The 820,122-byte publication map contains 105 milestones: 103 earned and two
deliberately unearned. It pins 2,530 theorem types and has SHA-256
`2935c7cb045d0f7ac2bb9baa98ffa7044543c410c84831fc9db36da66b47d157`.
The generated 2,060,926-byte status has SHA-256
`7b042bf47d86f20dbdb914d61c1ef84d39da0449692cde58cff223bcc50dcf3e`.
The canonical 215,538-byte TeX source has SHA-256
`2419f0f72282dc9c19762b0ee7a5ec438a6459901acc7d374ad9f42405921b6e`;
its deterministic 84-page, 453,006-byte A4 PDF has SHA-256
`438789317484ce2c73f194613f9906b9f3082b116d1129a0f97cdaf2330c321d`.

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
