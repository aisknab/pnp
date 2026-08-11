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

- Lean inventory: `PNP-LEAN-THEOREM-INVENTORY-2026-08-11-125`
- publication map: `PNP-FORMAL-PUBLICATION-MAP-2026-08-11-126`
- reconstruction status: `PNP-FORMAL-RECONSTRUCTION-STATUS-2026-08-11-126`
- public surface: `PUBLIC-SURFACE-BASELINE-2026-08-10-CONCRETE-LOCKED-NAND-THRESHOLD-121`
- canonical report: `PNP-CANONICAL-FORMAL-RECONSTRUCTION-REPORT-2026-08-11-126`

The compiled inventory records 27,129 declarations, 14,125 theorems, 7,249
assumption-free theorems, 14,995 excluded private declarations, 243
source-closure modules, and 2,523 reviewed milestone candidates. Its
17,551,864 canonical bytes have SHA-256
`fbd4614c550813bc8deff259f9442b37336efb40be3835e07880842c8e8a3be7`;
the exact Lean source closure has SHA-256
`c939e940c892279b3845b2d30dc0baa724d53b6f9a6249ccfa2900c7c00cb00f`.

The 817,481-byte publication map contains 104 milestones: 102 earned and two
deliberately unearned. It pins 2,523 theorem types and has SHA-256
`c4c3f6234e7bf80626d9e271991cea7ffdf00fe90c49c805c42e4a00628e59a3`.
The generated 2,054,365-byte status has SHA-256
`1e02d5abeb1d1b3138e8b59c4926a037c7653617720eb85a1efc25a1bb487cc8`.
The canonical 214,459-byte TeX source has SHA-256
`348ebff0df6ed0ce7eb27f1a529af88139a8dde58b13aad29433b9096ff321e3`;
its deterministic 84-page, 452,029-byte A4 PDF has SHA-256
`14f64fd605590edcb64d38314595db082b4916806c5ae3712977c7ab6cc47610`.

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
