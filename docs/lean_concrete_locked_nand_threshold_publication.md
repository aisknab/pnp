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

- Lean inventory: `PNP-LEAN-THEOREM-INVENTORY-2026-08-11-123`
- publication map: `PNP-FORMAL-PUBLICATION-MAP-2026-08-11-124`
- reconstruction status: `PNP-FORMAL-RECONSTRUCTION-STATUS-2026-08-11-124`
- public surface: `PUBLIC-SURFACE-BASELINE-2026-08-10-CONCRETE-LOCKED-NAND-THRESHOLD-121`
- canonical report: `PNP-CANONICAL-FORMAL-RECONSTRUCTION-REPORT-2026-08-11-124`

The compiled inventory records 26,624 declarations, 13,928 theorems, 7,165
assumption-free theorems, 14,939 excluded private declarations, 240
source-closure modules, and 2,498 reviewed milestone candidates. Its
17,275,021 canonical bytes have SHA-256
`231781715e011ebf8b583ce3c26f9896622d6962faaf8fcebd68f36e511ea003`;
the exact Lean source closure has SHA-256
`e30716e5e6ec0ad0f7c084a66d9ff28c1a8cf5a7008b5fc8caff81205e51eb15`.

The 809,177-byte publication map contains 102 milestones: 100 earned and two
deliberately unearned. It pins 2,498 theorem types and has SHA-256
`96e4a8b21a717e2190b5eed64ed50f27402b7690b7b80a52bb98782984f54258`.
The generated 2,034,357-byte status has SHA-256
`0f3e05664980c80d3c8a9fb5cceb4cb10cefaa05a96ea2d0f523c2663956fbc3`.
The canonical 211,420-byte TeX source has SHA-256
`b81fbdd17af61400d2883493ee90417affddd37f5d23567ede3d808bb417b0e2`;
its deterministic 82-page, 449,511-byte A4 PDF has SHA-256
`e998779d189f762ffcbcdb82b51de8a15bd0c7c8e4be6d463d5c833323ae45ef`.

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
