# Typed PCCPack generation and reflection

M188 replaces the two opaque report-bridge declarations
`PNP.GeneratePCCPack` and `PNP.CheckPCCPackexp` with transparent Lean
definitions. This is an assumption-removal milestone, not a proof of the
missing PCCMin certificate.

`PNP.PCCPack` now contains a canonical identifier and an explicit
`PNP.PCCMinLoopCertificate`. `GeneratePCCPack` preserves the supplied
certificate definitionally. `CheckPCCPackexp` accepts exactly the canonical
identifier, while the certificate's proof-bearing type prevents replacement by
a string handle or caller-supplied success flag.

The compiled M188 surface proves:

- every transparently generated package is accepted;
- the generated package contains exactly the supplied loop certificate;
- a package with a mismatched identifier is rejected; and
- the active report bridge consumes the explicit certificate without a
  generator/checker trust field.

The exact theorem inventory records `GeneratePCCPack` and `CheckPCCPackexp` as
definitions and records no project-specific axioms. Their theorem closures use
only the fixed Lean-standard allowlist (`propext` and `Quot.sound`).

This boundary does not construct a `PCCMinLoopCertificate`, validate historical
package bytes, prove the semantic adequacy of every certificate field, derive
unconditional ZeroSlack or PCCMin exactness, or establish encoded-size
polynomial construction and runtime. `CheckerTrustModel.satHard` remains an
explicit theorem premise. Deterministic CNFSAT in P, the eligible root theorem,
and all five global gates remain open.

## Verification

```bash
lake build PNP
lake env lean -DwarningAsError=true lean-audit/PNPTypedPCCPackReflectionAxiomAudit.lean
lake env lean -DwarningAsError=true lean-regression/PNPTypedPCCPackReflection.lean
node --test audits/lean-typed-pccpack-reflection0.test.mjs
node scripts/export-lean-theorem-inventory.mjs --check
node scripts/generate-formal-publication.mjs --check
```

The authoritative score change and evidence are recorded under checkpoints
`axiom-remove-generate-pccpack` and `axiom-remove-check-pccpackexp` in
[`status/PROOF_PROGRESS.json`](../status/PROOF_PROGRESS.json).
