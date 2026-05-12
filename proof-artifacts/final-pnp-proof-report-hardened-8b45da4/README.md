# Hardened final PNP proof-report artefact bundle

Source/checker revision:

- source commit: 8b45da4ed604a709d244c35acb886c5eee0889cd
- source tag: final-pnp-proof-report-hardened-8b45da4

Generated artefact JSON commit before metadata seal:

- c3d3915f7c37737924377076b9216efd2233037f

Sealed artefact release:

- sealed artefact tag: final-pnp-proof-report-artifacts-hardened-8b45da4-sealed
- bundle path: proof-artifacts/final-pnp-proof-report-hardened-8b45da4

Public theorem boundary:

```
CheckPCCPackexp(GeneratePCCPack())=accept => P = NP
```

Validation summary for this hardened release candidate:

```
tests=1043
pass=1043
fail=0
cancelled=0
skipped=0
todo=0
```

Verification modes:

1. Artefact verification checks this committed bundle against SHA256SUMS.
   SHA256SUMS does not contain a self-entry.
2. Regeneration verification reruns the proof-report writer and checks that
   CheckFinalPNPProofReport0 accepts with theorem statement P = NP and antecedent
   CheckPCCPackexp(GeneratePCCPack())=accept.
3. Exact release-context digest equality is required only when regenerating in
   the same clean release context.
